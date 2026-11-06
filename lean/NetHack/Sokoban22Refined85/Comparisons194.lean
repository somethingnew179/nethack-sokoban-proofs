/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27160 (p : Pattern) (guard : d5269 p = 1) : d3384 p ≤ (2 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27156 p hg
    simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27159 p hg
    simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27161 (p : Pattern) (guard : d5269 p = 1) : d3385 p ≤ (2 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27057 p hg
    simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27162 (p : Pattern) (guard : d5269 p = 1) : d3386 p ≤ (2 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27159 p hg
    simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27161 p hg
    simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27163 (p : Pattern) (guard : d5269 p = 1) : d3387 p ≤ (2 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27160 p hg
    simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27162 p hg
    simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27164 (p : Pattern) (guard : d5269 p = 1) : d3388 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27143 p hg
    simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27163 p hg
    simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27165 (p : Pattern) (guard : d0 p = 1) : d3390 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27166 (p : Pattern) (guard : d5269 p = 1) : d3391 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27165 p hg
    simpa only [d5269, d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27124 p hg
    simpa only [d5269, d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27167 (p : Pattern) (guard : d5269 p = 1) : d3392 p ≤ (2 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27166 p hg
    simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27168 (p : Pattern) (guard : d5269 p = 1) : d3393 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27167 p hg
    simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27129 p hg
    simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27169 (p : Pattern) (guard : d5269 p = 1) : d3394 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27148 p hg
    simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27170 (p : Pattern) (guard : d5269 p = 1) : d3395 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27168 p hg
    simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27171 (p : Pattern) (guard : d5269 p = 1) : d3396 p ≤ (2 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27138 p hg
    simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27047 p hg
    simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27172 (p : Pattern) (guard : d5269 p = 1) : d3397 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27170 p hg
    simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27171 p hg
    simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27173 (p : Pattern) (guard : d5269 p = 1) : d3398 p ≤ (2 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27138 p hg
    simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27174 (p : Pattern) (guard : d5269 p = 1) : d3399 p ≤ (2 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27173 p hg
    simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27175 (p : Pattern) (guard : d5269 p = 1) : d3400 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27172 p hg
    simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27174 p hg
    simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27176 (p : Pattern) (guard : d5269 p = 1) : d3401 p ≤ (2 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27177 (p : Pattern) (guard : d5269 p = 1) : d3402 p ≤ (2 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27155 p hg
    simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27176 p hg
    simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27178 (p : Pattern) (guard : d5269 p = 1) : d3403 p ≤ (2 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27158 p hg
    simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27057 p hg
    simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27179 (p : Pattern) (guard : d5269 p = 1) : d3404 p ≤ (2 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27177 p hg
    simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27178 p hg
    simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27180 (p : Pattern) (guard : d5269 p = 1) : d3405 p ≤ (2 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27158 p hg
    simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27059 p hg
    simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27181 (p : Pattern) (guard : d5269 p = 1) : d3406 p ≤ (2 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27180 p hg
    simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27182 (p : Pattern) (guard : d5269 p = 1) : d3407 p ≤ (2 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27179 p hg
    simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27181 p hg
    simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27183 (p : Pattern) (guard : d5269 p = 1) : d3408 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27175 p hg
    simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27182 p hg
    simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27184 (p : Pattern) (guard : d5269 p = 1) : d3409 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27164 p hg
    simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27183 p hg
    simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27185 (p : Pattern) (guard : d5269 p = 1) : d3410 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27131 p hg
    simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27139 p hg
    simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27186 (p : Pattern) (guard : d5269 p = 1) : d3411 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27185 p hg
    simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27142 p hg
    simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27187 (p : Pattern) (guard : d5269 p = 1) : d3412 p ≤ (2 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27153 p hg
    simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27154 p hg
    simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27188 (p : Pattern) (guard : d5269 p = 1) : d3413 p ≤ (2 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27187 p hg
    simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27189 (p : Pattern) (guard : d5269 p = 1) : d3414 p ≤ (2 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27188 p hg
    simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27190 (p : Pattern) (guard : d5269 p = 1) : d3415 p ≤ (2 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27189 p hg
    simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27191 (p : Pattern) (guard : d5269 p = 1) : d3416 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27186 p hg
    simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27190 p hg
    simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27192 (p : Pattern) (guard : d5269 p = 1) : d3417 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27131 p hg
    simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27193 (p : Pattern) (guard : d5269 p = 1) : d3418 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27192 p hg
    simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27171 p hg
    simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27194 (p : Pattern) (guard : d5269 p = 1) : d3419 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27193 p hg
    simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27174 p hg
    simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27195 (p : Pattern) (guard : d5269 p = 1) : d3420 p ≤ (2 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27187 p hg
    simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27196 (p : Pattern) (guard : d5269 p = 1) : d3421 p ≤ (2 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27195 p hg
    simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27197 (p : Pattern) (guard : d5269 p = 1) : d3422 p ≤ (2 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27196 p hg
    simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27198 (p : Pattern) (guard : d5269 p = 1) : d3423 p ≤ (2 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27194 p hg
    simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27197 p hg
    simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27199 (p : Pattern) (guard : d5269 p = 1) : d3424 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27191 p hg
    simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27198 p hg
    simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27200 (p : Pattern) (guard : d5269 p = 1) : d3425 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27184 p hg
    simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27199 p hg
    simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27201 (p : Pattern) (guard : d5269 p = 1) : d3426 p ≤ (2 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27141 p hg
    simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27202 (p : Pattern) (guard : d5269 p = 1) : d3427 p ≤ (2 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27201 p hg
    simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27203 (p : Pattern) (guard : d5269 p = 1) : d3428 p ≤ (2 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27202 p hg
    simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27204 (p : Pattern) (guard : d5269 p = 1) : d3429 p ≤ (2 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27203 p hg
    simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27205 (p : Pattern) (guard : d5269 p = 1) : d3430 p ≤ (2 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27199 p hg
    simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27204 p hg
    simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27206 (p : Pattern) (guard : d5269 p = 1) : d3431 p ≤ (2 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27200 p hg
    simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27205 p hg
    simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27207 (p : Pattern) (guard : d5269 p = 1) : d3432 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27186 p hg
    simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27163 p hg
    simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27208 (p : Pattern) (guard : d5269 p = 1) : d3433 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27194 p hg
    simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27182 p hg
    simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27209 (p : Pattern) (guard : d5269 p = 1) : d3434 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27207 p hg
    simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27208 p hg
    simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27210 (p : Pattern) (guard : d5269 p = 1) : d3435 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27209 p hg
    simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27199 p hg
    simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27211 (p : Pattern) (guard : d5269 p = 1) : d3436 p ≤ (2 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27199 p hg
    simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27212 (p : Pattern) (guard : d5269 p = 1) : d3437 p ≤ (2 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27210 p hg
    simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27211 p hg
    simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27213 (p : Pattern) (guard : d5269 p = 1) : d3438 p ≤ (2 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27206 p hg
    simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27212 p hg
    simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27214 (p : Pattern) (guard : d5269 p = 1) : d3439 p ≤ (2 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27100 p hg
    simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27213 p hg
    simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27215 (p : Pattern) (guard : d5269 p = 1) : d3440 p ≤ (2 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27121 p hg
    simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27214 p hg
    simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27216 (p : Pattern) (guard : d5269 p = 1) : d3441 p ≤ (2 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27008 p hg
    simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27015 p hg
    simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27217 (p : Pattern) (guard : d5269 p = 1) : d3442 p ≤ (2 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27038 p hg
    simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27216 p hg
    simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27218 (p : Pattern) (guard : d5269 p = 1) : d3443 p ≤ (2 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27008 p hg
    simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27022 p hg
    simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27219 (p : Pattern) (guard : d5269 p = 1) : d3444 p ≤ (2 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27014 p hg
    simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27220 (p : Pattern) (guard : d5269 p = 1) : d3445 p ≤ (2 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27218 p hg
    simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27219 p hg
    simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27221 (p : Pattern) (guard : d5269 p = 1) : d3446 p ≤ (2 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27217 p hg
    simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27220 p hg
    simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27222 (p : Pattern) (guard : d5269 p = 1) : d3447 p ≤ (2 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27053 p hg
    simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27219 p hg
    simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27223 (p : Pattern) (guard : d5269 p = 1) : d3448 p ≤ (2 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27222 p hg
    simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27060 p hg
    simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27224 (p : Pattern) (guard : d5269 p = 1) : d3449 p ≤ (2 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27221 p hg
    simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27223 p hg
    simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27225 (p : Pattern) (guard : d5269 p = 1) : d3450 p ≤ (2 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27066 p hg
    simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27224 p hg
    simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27226 (p : Pattern) (guard : d5269 p = 1) : d3451 p ≤ (2 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27216 p hg
    simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27227 (p : Pattern) (guard : d5269 p = 1) : d3452 p ≤ (2 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27219 p hg
    simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27059 p hg
    simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27228 (p : Pattern) (guard : d5269 p = 1) : d3453 p ≤ (2 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27226 p hg
    simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27227 p hg
    simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27229 (p : Pattern) (guard : d5269 p = 1) : d3454 p ≤ (2 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27219 p hg
    simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27230 (p : Pattern) (guard : d5269 p = 1) : d3455 p ≤ (2 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27229 p hg
    simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27231 (p : Pattern) (guard : d5269 p = 1) : d3456 p ≤ (2 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27228 p hg
    simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27230 p hg
    simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27232 (p : Pattern) (guard : d5269 p = 1) : d3457 p ≤ (2 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27074 p hg
    simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27231 p hg
    simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27233 (p : Pattern) (guard : d5269 p = 1) : d3458 p ≤ (2 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27225 p hg
    simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27232 p hg
    simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27234 (p : Pattern) (guard : d5269 p = 1) : d3459 p ≤ (2 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26987 p hg
    simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27068 p hg
    simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27235 (p : Pattern) (guard : d5269 p = 1) : d3460 p ≤ (2 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27234 p hg
    simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27069 p hg
    simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27236 (p : Pattern) (guard : d0 p = 1) : d3461 p ≤ (2 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27237 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27238 (p : Pattern) (guard : d5268 p = 1) : d3461 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16154 p hg
    simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27237 p hg
    simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27239 (p : Pattern) (guard : d5269 p = 1) : d3461 p ≤ (2 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27236 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27238 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27240 (p : Pattern) (guard : d5269 p = 1) : d3462 p ≤ (2 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27239 p hg
    simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27241 (p : Pattern) (guard : d5269 p = 1) : d3463 p ≤ (2 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27239 p hg
    simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27240 p hg
    simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27242 (p : Pattern) (guard : d5269 p = 1) : d3464 p ≤ (2 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26993 p hg
    simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27241 p hg
    simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27243 (p : Pattern) (guard : d5269 p = 1) : d3465 p ≤ (2 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27242 p hg
    simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27244 (p : Pattern) (guard : d5269 p = 1) : d3466 p ≤ (2 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27243 p hg
    simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27245 (p : Pattern) (guard : d5269 p = 1) : d3467 p ≤ (2 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27235 p hg
    simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27244 p hg
    simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27246 (p : Pattern) (guard : d5269 p = 1) : d3468 p ≤ (2 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26993 p hg
    simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27247 (p : Pattern) (guard : d5269 p = 1) : d3469 p ≤ (2 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27038 p hg
    simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27246 p hg
    simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27248 (p : Pattern) (guard : d5269 p = 1) : d3470 p ≤ (2 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27247 p hg
    simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27076 p hg
    simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27249 (p : Pattern) (guard : d5269 p = 1) : d3471 p ≤ (2 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27241 p hg
    simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27250 (p : Pattern) (guard : d5269 p = 1) : d3472 p ≤ (2 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27249 p hg
    simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27251 (p : Pattern) (guard : d5269 p = 1) : d3473 p ≤ (2 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27250 p hg
    simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27252 (p : Pattern) (guard : d5269 p = 1) : d3474 p ≤ (2 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27248 p hg
    simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27251 p hg
    simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27253 (p : Pattern) (guard : d5269 p = 1) : d3475 p ≤ (2 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27245 p hg
    simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27252 p hg
    simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27254 (p : Pattern) (guard : d5269 p = 1) : d3476 p ≤ (2 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27233 p hg
    simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27253 p hg
    simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27255 (p : Pattern) (guard : d5269 p = 1) : d3477 p ≤ (2 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27253 p hg
    simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27256 (p : Pattern) (guard : d5269 p = 1) : d3478 p ≤ (2 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27254 p hg
    simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27255 p hg
    simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27257 (p : Pattern) (guard : d5269 p = 1) : d3479 p ≤ (2 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27115 p hg
    simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27256 p hg
    simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27258 (p : Pattern) (guard : d5269 p = 1) : d3480 p ≤ (2 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27100 p hg
    simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27257 p hg
    simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27259 (p : Pattern) (guard : d5269 p = 1) : d3481 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27138 p hg
    simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27260 (p : Pattern) (guard : d5269 p = 1) : d3482 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27170 p hg
    simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27259 p hg
    simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27261 (p : Pattern) (guard : d5269 p = 1) : d3483 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27259 p hg
    simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27262 (p : Pattern) (guard : d5269 p = 1) : d3484 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27260 p hg
    simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27261 p hg
    simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27263 (p : Pattern) (guard : d5269 p = 1) : d3485 p ≤ (2 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27158 p hg
    simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27264 (p : Pattern) (guard : d5269 p = 1) : d3486 p ≤ (2 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27177 p hg
    simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27263 p hg
    simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27265 (p : Pattern) (guard : d5269 p = 1) : d3487 p ≤ (2 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27263 p hg
    simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27266 (p : Pattern) (guard : d5269 p = 1) : d3488 p ≤ (2 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27264 p hg
    simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27265 p hg
    simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27267 (p : Pattern) (guard : d5269 p = 1) : d3489 p ≤ (2 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27262 p hg
    simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27266 p hg
    simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27268 (p : Pattern) (guard : d5269 p = 1) : d3490 p ≤ (2 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27164 p hg
    simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27267 p hg
    simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27269 (p : Pattern) (guard : d5269 p = 1) : d3491 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27192 p hg
    simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27259 p hg
    simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27270 (p : Pattern) (guard : d5269 p = 1) : d3492 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27269 p hg
    simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27261 p hg
    simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27271 (p : Pattern) (guard : d5269 p = 1) : d3493 p ≤ (2 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27270 p hg
    simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27197 p hg
    simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27272 (p : Pattern) (guard : d5269 p = 1) : d3494 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27191 p hg
    simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27271 p hg
    simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27273 (p : Pattern) (guard : d5269 p = 1) : d3495 p ≤ (2 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27268 p hg
    simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27272 p hg
    simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27274 (p : Pattern) (guard : d5269 p = 1) : d3496 p ≤ (2 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27272 p hg
    simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27204 p hg
    simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27275 (p : Pattern) (guard : d5269 p = 1) : d3497 p ≤ (2 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27273 p hg
    simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27274 p hg
    simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27276 (p : Pattern) (guard : d5269 p = 1) : d3498 p ≤ (2 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27154 p hg
    simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27277 (p : Pattern) (guard : d5269 p = 1) : d3499 p ≤ (2 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27276 p hg
    simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27278 (p : Pattern) (guard : d5269 p = 1) : d3500 p ≤ (2 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27277 p hg
    simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27263 p hg
    simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27279 (p : Pattern) (guard : d5269 p = 1) : d3501 p ≤ (2 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27153 p hg
    simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27280 (p : Pattern) (guard : d5269 p = 1) : d3502 p ≤ (2 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27279 p hg
    simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27281 (p : Pattern) (guard : d5269 p = 1) : d3503 p ≤ (2 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27280 p hg
    simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27282 (p : Pattern) (guard : d5269 p = 1) : d3504 p ≤ (2 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27278 p hg
    simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27281 p hg
    simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27283 (p : Pattern) (guard : d5269 p = 1) : d3505 p ≤ (2 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27186 p hg
    simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27282 p hg
    simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27284 (p : Pattern) (guard : d5269 p = 1) : d3506 p ≤ (2 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27136 p hg
    simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27154 p hg
    simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27285 (p : Pattern) (guard : d5269 p = 1) : d3507 p ≤ (2 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27284 p hg
    simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27158 p hg
    simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27286 (p : Pattern) (guard : d5269 p = 1) : d3508 p ≤ (2 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27285 p hg
    simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27280 p hg
    simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27287 (p : Pattern) (guard : d5269 p = 1) : d3509 p ≤ (2 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27030 p hg
    simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27288 (p : Pattern) (guard : d5269 p = 1) : d3510 p ≤ (2 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27286 p hg
    simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27287 p hg
    simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27289 (p : Pattern) (guard : d5269 p = 1) : d3511 p ≤ (2 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27270 p hg
    simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27288 p hg
    simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27290 (p : Pattern) (guard : d5269 p = 1) : d3512 p ≤ (2 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27283 p hg
    simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27289 p hg
    simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27291 (p : Pattern) (guard : d5269 p = 1) : d3513 p ≤ (2 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27292 (p : Pattern) (guard : d5269 p = 1) : d3514 p ≤ (2 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27131 p hg
    simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27291 p hg
    simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27293 (p : Pattern) (guard : d5269 p = 1) : d3515 p ≤ (2 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27292 p hg
    simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27174 p hg
    simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27294 (p : Pattern) (guard : d5269 p = 1) : d3516 p ≤ (2 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27293 p hg
    simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27197 p hg
    simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27295 (p : Pattern) (guard : d5269 p = 1) : d3517 p ≤ (2 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27259 p hg
    simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27296 (p : Pattern) (guard : d5269 p = 1) : d3518 p ≤ (2 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27295 p hg
    simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27196 p hg
    simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27297 (p : Pattern) (guard : d5269 p = 1) : d3519 p ≤ (2 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27002 p hg
    simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27298 (p : Pattern) (guard : d5269 p = 1) : d3520 p ≤ (2 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27297 p hg
    simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27299 (p : Pattern) (guard : d5269 p = 1) : d3521 p ≤ (2 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27296 p hg
    simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27298 p hg
    simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
