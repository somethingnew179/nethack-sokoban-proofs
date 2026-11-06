import NetHack.Soko22Hazard87.Compare108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27250 (p : Pattern) (guard : d188187 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17238 p = 1 := by simpa only [d188187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27099 p hg
    simpa only [d188187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19530 p = 1 := by simpa only [d188187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27249 p hg
    simpa only [d188187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27251 (p : Pattern) (guard : d188188 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188187 p = 1 := by simpa only [d188188, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27250 p hg
    simpa only [d188188, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188188, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188188, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27252 (p : Pattern) (guard : d188189 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188189, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188189, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188188 p = 1 := by simpa only [d188189, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27251 p hg
    simpa only [d188189, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27253 (p : Pattern) (guard : d17242 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17167 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27097 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27254 (p : Pattern) (guard : d17243 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27098 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17242 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27253 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27255 (p : Pattern) (guard : d19536 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19528 p = 1 := by simpa only [d19536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27247 p hg
    simpa only [d19536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27256 (p : Pattern) (guard : d19537 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19529 p = 1 := by simpa only [d19537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27248 p hg
    simpa only [d19537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19536 p = 1 := by simpa only [d19537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27255 p hg
    simpa only [d19537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27257 (p : Pattern) (guard : d188190 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17243 p = 1 := by simpa only [d188190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27254 p hg
    simpa only [d188190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19537 p = 1 := by simpa only [d188190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27256 p hg
    simpa only [d188190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27258 (p : Pattern) (guard : d188191 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188190 p = 1 := by simpa only [d188191, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27257 p hg
    simpa only [d188191, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188191, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188191, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27259 (p : Pattern) (guard : d188192 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188192, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188192, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188191 p = 1 := by simpa only [d188192, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27258 p hg
    simpa only [d188192, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27260 (p : Pattern) (guard : d188193 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188189 p = 1 := by simpa only [d188193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27252 p hg
    simpa only [d188193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188192 p = 1 := by simpa only [d188193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27259 p hg
    simpa only [d188193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27261 (p : Pattern) (guard : d188194 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188193 p = 1 := by simpa only [d188194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27260 p hg
    simpa only [d188194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27262 (p : Pattern) (guard : d188195 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188194 p = 1 := by simpa only [d188195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27261 p hg
    simpa only [d188195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27263 (p : Pattern) (guard : d188196 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188195 p = 1 := by simpa only [d188196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27262 p hg
    simpa only [d188196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27264 (p : Pattern) (guard : d2060 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27080 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27265 (p : Pattern) (guard : d2062 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27264 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27026 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27266 (p : Pattern) (guard : d2063 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27265 p hg
    simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27267 (p : Pattern) (guard : d2064 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27054 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27266 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27268 (p : Pattern) (guard : d2065 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27267 p hg
    simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27269 (p : Pattern) (guard : d2066 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27268 p hg
    simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27270 (p : Pattern) (guard : d2067 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27269 p hg
    simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27271 (p : Pattern) (guard : d2068 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27270 p hg
    simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27272 (p : Pattern) (guard : d2071 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27271 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27273 (p : Pattern) (guard : d15563 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27272 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27093 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27274 (p : Pattern) (guard : d17169 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27066 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27273 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27275 (p : Pattern) (guard : d17170 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27274 p hg
    simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27276 (p : Pattern) (guard : d17171 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27275 p hg
    simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27277 (p : Pattern) (guard : d17172 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27276 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27278 (p : Pattern) (guard : d17177 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27277 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27279 (p : Pattern) (guard : d2060 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27230 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27174 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27280 (p : Pattern) (guard : d2062 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27279 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27176 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27281 (p : Pattern) (guard : d2063 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27280 p hg
    simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27282 (p : Pattern) (guard : d2064 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27204 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27281 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27283 (p : Pattern) (guard : d2065 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27282 p hg
    simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27284 (p : Pattern) (guard : d2066 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27283 p hg
    simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27285 (p : Pattern) (guard : d2067 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27284 p hg
    simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27286 (p : Pattern) (guard : d2068 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27285 p hg
    simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27287 (p : Pattern) (guard : d2071 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27286 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27288 (p : Pattern) (guard : d15563 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27287 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27243 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27289 (p : Pattern) (guard : d17169 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27216 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27288 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27290 (p : Pattern) (guard : d19555 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17169 p = 1 := by simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27289 p hg
    simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27291 (p : Pattern) (guard : d19556 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19555 p = 1 := by simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27290 p hg
    simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27292 (p : Pattern) (guard : d19557 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19556 p = 1 := by simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27291 p hg
    simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27293 (p : Pattern) (guard : d19558 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19557 p = 1 := by simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27292 p hg
    simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27294 (p : Pattern) (guard : d188197 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27278 p hg
    simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19558 p = 1 := by simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27293 p hg
    simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27295 (p : Pattern) (guard : d188198 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188197 p = 1 := by simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27294 p hg
    simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27296 (p : Pattern) (guard : d188199 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188198 p = 1 := by simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27295 p hg
    simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27297 (p : Pattern) (guard : d188200 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188192 p = 1 := by simpa only [d188200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27259 p hg
    simpa only [d188200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188199 p = 1 := by simpa only [d188200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27296 p hg
    simpa only [d188200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27298 (p : Pattern) (guard : d188201 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188200 p = 1 := by simpa only [d188201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27297 p hg
    simpa only [d188201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27299 (p : Pattern) (guard : d188202 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188201 p = 1 := by simpa only [d188202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27298 p hg
    simpa only [d188202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27300 (p : Pattern) (guard : d188203 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188202 p = 1 := by simpa only [d188203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27299 p hg
    simpa only [d188203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27301 (p : Pattern) (guard : d188204 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188196 p = 1 := by simpa only [d188204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27263 p hg
    simpa only [d188204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188203 p = 1 := by simpa only [d188204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27300 p hg
    simpa only [d188204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27302 (p : Pattern) (guard : d188205 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188204 p = 1 := by simpa only [d188205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27301 p hg
    simpa only [d188205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27303 (p : Pattern) (guard : d13614 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27272 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27304 (p : Pattern) (guard : d17294 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27066 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13614 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27303 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27305 (p : Pattern) (guard : d17295 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d17295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17294 p = 1 := by simpa only [d17295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27304 p hg
    simpa only [d17295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27306 (p : Pattern) (guard : d17296 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d17296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17295 p = 1 := by simpa only [d17296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27305 p hg
    simpa only [d17296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27307 (p : Pattern) (guard : d17297 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17296 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27306 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27308 (p : Pattern) (guard : d17298 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27098 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17297 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27307 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27309 (p : Pattern) (guard : d13614 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27287 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27310 (p : Pattern) (guard : d17294 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27216 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13614 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27309 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27311 (p : Pattern) (guard : d19650 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17294 p = 1 := by simpa only [d19650, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27310 p hg
    simpa only [d19650, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19650, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19650, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27312 (p : Pattern) (guard : d19651 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19651, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19651, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19650 p = 1 := by simpa only [d19651, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27311 p hg
    simpa only [d19651, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27313 (p : Pattern) (guard : d19652 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19651 p = 1 := by simpa only [d19652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27312 p hg
    simpa only [d19652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27314 (p : Pattern) (guard : d19653 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19529 p = 1 := by simpa only [d19653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27248 p hg
    simpa only [d19653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19652 p = 1 := by simpa only [d19653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27313 p hg
    simpa only [d19653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27315 (p : Pattern) (guard : d188206 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17298 p = 1 := by simpa only [d188206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27308 p hg
    simpa only [d188206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19653 p = 1 := by simpa only [d188206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27314 p hg
    simpa only [d188206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27316 (p : Pattern) (guard : d188207 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188206 p = 1 := by simpa only [d188207, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27315 p hg
    simpa only [d188207, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188207, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188207, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27317 (p : Pattern) (guard : d188208 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188208, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188208, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188207 p = 1 := by simpa only [d188208, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27316 p hg
    simpa only [d188208, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27318 (p : Pattern) (guard : d188209 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188208 p = 1 := by simpa only [d188209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27317 p hg
    simpa only [d188209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27319 (p : Pattern) (guard : d188210 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188209 p = 1 := by simpa only [d188210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27318 p hg
    simpa only [d188210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27320 (p : Pattern) (guard : d188211 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188210 p = 1 := by simpa only [d188211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d188211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27321 (p : Pattern) (guard : d188212 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188211 p = 1 := by simpa only [d188212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27320 p hg
    simpa only [d188212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27322 (p : Pattern) (guard : d188213 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188212 p = 1 := by simpa only [d188213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27321 p hg
    simpa only [d188213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27323 (p : Pattern) (guard : d188214 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188213 p = 1 := by simpa only [d188214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27322 p hg
    simpa only [d188214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27324 (p : Pattern) (guard : d188215 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188205 p = 1 := by simpa only [d188215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27302 p hg
    simpa only [d188215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188214 p = 1 := by simpa only [d188215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27323 p hg
    simpa only [d188215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27325 (p : Pattern) (guard : d188216 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188215 p = 1 := by simpa only [d188216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27324 p hg
    simpa only [d188216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27326 (p : Pattern) (guard : d188217 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188216 p = 1 := by simpa only [d188217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27325 p hg
    simpa only [d188217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27327 (p : Pattern) (guard : d188218 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188218, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188218, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188217 p = 1 := by simpa only [d188218, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27326 p hg
    simpa only [d188218, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27328 (p : Pattern) (guard : d188219 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188218 p = 1 := by simpa only [d188219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27327 p hg
    simpa only [d188219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27329 (p : Pattern) (guard : d188220 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188199 p = 1 := by simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27296 p hg
    simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27330 (p : Pattern) (guard : d188221 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188220 p = 1 := by simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27331 (p : Pattern) (guard : d188222 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188221 p = 1 := by simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27330 p hg
    simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27332 (p : Pattern) (guard : d188223 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188222 p = 1 := by simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27331 p hg
    simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27333 (p : Pattern) (guard : d188224 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188223 p = 1 := by simpa only [d188224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27332 p hg
    simpa only [d188224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27334 (p : Pattern) (guard : d188225 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188224 p = 1 := by simpa only [d188225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27333 p hg
    simpa only [d188225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27335 (p : Pattern) (guard : d188226 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188225 p = 1 := by simpa only [d188226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27334 p hg
    simpa only [d188226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27336 (p : Pattern) (guard : d188227 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188226 p = 1 := by simpa only [d188227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27335 p hg
    simpa only [d188227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27337 (p : Pattern) (guard : d188228 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188227 p = 1 := by simpa only [d188228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27336 p hg
    simpa only [d188228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27338 (p : Pattern) (guard : d188229 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188229, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188229, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188228 p = 1 := by simpa only [d188229, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27337 p hg
    simpa only [d188229, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27339 (p : Pattern) (guard : d188230 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188229 p = 1 := by simpa only [d188230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27338 p hg
    simpa only [d188230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27340 (p : Pattern) (guard : d188231 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188219 p = 1 := by simpa only [d188231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27328 p hg
    simpa only [d188231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188230 p = 1 := by simpa only [d188231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27339 p hg
    simpa only [d188231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27341 (p : Pattern) (guard : d188232 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188231 p = 1 := by simpa only [d188232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27340 p hg
    simpa only [d188232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27342 (p : Pattern) (guard : d188233 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188232 p = 1 := by simpa only [d188233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27341 p hg
    simpa only [d188233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27343 (p : Pattern) (guard : d188234 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188233 p = 1 := by simpa only [d188234, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27342 p hg
    simpa only [d188234, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188234, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d188234, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27344 (p : Pattern) (guard : d188235 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188235, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d188235, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188234 p = 1 := by simpa only [d188235, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27343 p hg
    simpa only [d188235, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27345 (p : Pattern) (guard : d188236 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188235 p = 1 := by simpa only [d188236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27344 p hg
    simpa only [d188236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27346 (p : Pattern) (guard : d188237 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188236 p = 1 := by simpa only [d188237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27345 p hg
    simpa only [d188237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27347 (p : Pattern) (guard : d188238 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188237 p = 1 := by simpa only [d188238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27346 p hg
    simpa only [d188238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27348 (p : Pattern) (guard : d188239 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188238 p = 1 := by simpa only [d188239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27347 p hg
    simpa only [d188239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27349 (p : Pattern) (guard : d188240 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188239 p = 1 := by simpa only [d188240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27348 p hg
    simpa only [d188240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27350 (p : Pattern) (guard : d188241 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188240 p = 1 := by simpa only [d188241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27349 p hg
    simpa only [d188241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27351 (p : Pattern) (guard : d188242 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188241 p = 1 := by simpa only [d188242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27350 p hg
    simpa only [d188242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27352 (p : Pattern) (guard : d188243 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188242 p = 1 := by simpa only [d188243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27351 p hg
    simpa only [d188243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27353 (p : Pattern) (guard : d188244 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188243 p = 1 := by simpa only [d188244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27352 p hg
    simpa only [d188244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27354 (p : Pattern) (guard : d188245 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188244 p = 1 := by simpa only [d188245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27353 p hg
    simpa only [d188245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27355 (p : Pattern) (guard : d188246 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d188186 p = 1 := by simpa only [d188246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26949 p hg
    simpa only [d188246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188245 p = 1 := by simpa only [d188246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27354 p hg
    simpa only [d188246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27356 (p : Pattern) (guard : d188247 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 260 with
  | false =>
    have hg : d188246 p = 1 := by simpa only [d188247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27355 p hg
    simpa only [d188247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27357 (p : Pattern) (guard : d188248 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 259 with
  | false =>
    have hg : d188247 p = 1 := by simpa only [d188248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27356 p hg
    simpa only [d188248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27358 (p : Pattern) (guard : d188249 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 258 with
  | false =>
    have hg : d188248 p = 1 := by simpa only [d188249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27357 p hg
    simpa only [d188249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27359 (p : Pattern) (guard : d188250 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 257 with
  | false =>
    have hg : d188249 p = 1 := by simpa only [d188250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27358 p hg
    simpa only [d188250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27360 (p : Pattern) (guard : d188251 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 256 with
  | false =>
    have hg : d188250 p = 1 := by simpa only [d188251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27359 p hg
    simpa only [d188251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27361 (p : Pattern) (guard : d188252 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 255 with
  | false =>
    have hg : d188251 p = 1 := by simpa only [d188252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27360 p hg
    simpa only [d188252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27362 (p : Pattern) (guard : d188253 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 254 with
  | false =>
    have hg : d188252 p = 1 := by simpa only [d188253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27361 p hg
    simpa only [d188253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27363 (p : Pattern) (guard : d188254 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 253 with
  | false =>
    have hg : d188253 p = 1 := by simpa only [d188254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27362 p hg
    simpa only [d188254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27364 (p : Pattern) (guard : d188255 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 252 with
  | false =>
    have hg : d188254 p = 1 := by simpa only [d188255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27363 p hg
    simpa only [d188255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27365 (p : Pattern) (guard : d188256 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 251 with
  | false =>
    have hg : d188255 p = 1 := by simpa only [d188256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27364 p hg
    simpa only [d188256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27366 (p : Pattern) (guard : d188257 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 250 with
  | false =>
    have hg : d188256 p = 1 := by simpa only [d188257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27365 p hg
    simpa only [d188257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27367 (p : Pattern) (guard : d188258 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 249 with
  | false =>
    have hg : d188257 p = 1 := by simpa only [d188258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27366 p hg
    simpa only [d188258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27368 (p : Pattern) (guard : d188259 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 245 with
  | false =>
    have hg : d188258 p = 1 := by simpa only [d188259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27367 p hg
    simpa only [d188259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27369 (p : Pattern) (guard : d188260 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 200 with
  | false =>
    have hg : d188259 p = 1 := by simpa only [d188260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27368 p hg
    simpa only [d188260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27370 (p : Pattern) (guard : d188261 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 199 with
  | false =>
    have hg : d188260 p = 1 := by simpa only [d188261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27369 p hg
    simpa only [d188261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27371 (p : Pattern) (guard : d188262 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 186 with
  | false =>
    have hg : d188261 p = 1 := by simpa only [d188262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27370 p hg
    simpa only [d188262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27372 (p : Pattern) (guard : d188263 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 185 with
  | false =>
    have hg : d188262 p = 1 := by simpa only [d188263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27371 p hg
    simpa only [d188263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27373 (p : Pattern) (guard : d188264 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 184 with
  | false =>
    have hg : d188263 p = 1 := by simpa only [d188264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27372 p hg
    simpa only [d188264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27374 (p : Pattern) (guard : d188265 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 181 with
  | false =>
    have hg : d188264 p = 1 := by simpa only [d188265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27373 p hg
    simpa only [d188265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27375 (p : Pattern) (guard : d188266 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 177 with
  | false =>
    have hg : d188265 p = 1 := by simpa only [d188266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27374 p hg
    simpa only [d188266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27376 (p : Pattern) (guard : d188267 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 164 with
  | false =>
    have hg : d188266 p = 1 := by simpa only [d188267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27375 p hg
    simpa only [d188267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27377 (p : Pattern) (guard : d188268 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 156 with
  | false =>
    have hg : d188267 p = 1 := by simpa only [d188268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27376 p hg
    simpa only [d188268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27378 (p : Pattern) (guard : d188269 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 155 with
  | false =>
    have hg : d188268 p = 1 := by simpa only [d188269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27377 p hg
    simpa only [d188269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27379 (p : Pattern) (guard : d188270 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 134 with
  | false =>
    have hg : d188269 p = 1 := by simpa only [d188270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27378 p hg
    simpa only [d188270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27380 (p : Pattern) (guard : d188271 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 133 with
  | false =>
    have hg : d188270 p = 1 := by simpa only [d188271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27379 p hg
    simpa only [d188271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27381 (p : Pattern) (guard : d188272 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 120 with
  | false =>
    have hg : d188271 p = 1 := by simpa only [d188272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27380 p hg
    simpa only [d188272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27382 (p : Pattern) (guard : d188273 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 118 with
  | false =>
    have hg : d188272 p = 1 := by simpa only [d188273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27381 p hg
    simpa only [d188273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27383 (p : Pattern) (guard : d188274 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 114 with
  | false =>
    have hg : d188273 p = 1 := by simpa only [d188274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27382 p hg
    simpa only [d188274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27384 (p : Pattern) (guard : d188275 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 111 with
  | false =>
    have hg : d188274 p = 1 := by simpa only [d188275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27383 p hg
    simpa only [d188275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27385 (p : Pattern) (guard : d188276 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 98 with
  | false =>
    have hg : d188275 p = 1 := by simpa only [d188276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27384 p hg
    simpa only [d188276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27386 (p : Pattern) (guard : d188277 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 97 with
  | false =>
    have hg : d188276 p = 1 := by simpa only [d188277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27385 p hg
    simpa only [d188277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27387 (p : Pattern) (guard : d188278 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 94 with
  | false =>
    have hg : d188277 p = 1 := by simpa only [d188278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27386 p hg
    simpa only [d188278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27388 (p : Pattern) (guard : d188279 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 76 with
  | false =>
    have hg : d188278 p = 1 := by simpa only [d188279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27387 p hg
    simpa only [d188279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27389 (p : Pattern) (guard : d188280 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 67 with
  | false =>
    have hg : d188279 p = 1 := by simpa only [d188280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27388 p hg
    simpa only [d188280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27390 (p : Pattern) (guard : d188281 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 52 with
  | false =>
    have hg : d188280 p = 1 := by simpa only [d188281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27389 p hg
    simpa only [d188281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27391 (p : Pattern) (guard : d188282 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 47 with
  | false =>
    have hg : d188281 p = 1 := by simpa only [d188282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27390 p hg
    simpa only [d188282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27392 (p : Pattern) (guard : d188283 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 46 with
  | false =>
    have hg : d188282 p = 1 := by simpa only [d188283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27391 p hg
    simpa only [d188283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27393 (p : Pattern) (guard : d188284 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 45 with
  | false =>
    have hg : d188283 p = 1 := by simpa only [d188284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27392 p hg
    simpa only [d188284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27394 (p : Pattern) (guard : d188285 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 30 with
  | false =>
    have hg : d188284 p = 1 := by simpa only [d188285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27393 p hg
    simpa only [d188285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27395 (p : Pattern) (guard : d188286 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 29 with
  | false =>
    have hg : d188285 p = 1 := by simpa only [d188286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27394 p hg
    simpa only [d188286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27396 (p : Pattern) (guard : d188287 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 28 with
  | false =>
    have hg : d188286 p = 1 := by simpa only [d188287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27395 p hg
    simpa only [d188287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27397 (p : Pattern) (guard : d188288 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 27 with
  | false =>
    have hg : d188287 p = 1 := by simpa only [d188288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27396 p hg
    simpa only [d188288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27398 (p : Pattern) (guard : d188289 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 25 with
  | false =>
    have hg : d188288 p = 1 := by simpa only [d188289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27397 p hg
    simpa only [d188289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27399 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27400 (p : Pattern) (guard : d0 p = 1) : d48697 p ≤ (-2 : Int) + d188502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27401 (p : Pattern) (guard : d0 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27402 (p : Pattern) (guard : d0 p = 1) : d48613 p ≤ (-2 : Int) + d188495 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27403 (p : Pattern) (guard : d0 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27404 (p : Pattern) (guard : d0 p = 1) : d48630 p ≤ (-2 : Int) + d188492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27405 (p : Pattern) (guard : d0 p = 1) : d48635 p ≤ (-2 : Int) + d188488 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27406 (p : Pattern) (guard : d0 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27407 (p : Pattern) (guard : d0 p = 1) : d48567 p ≤ (-2 : Int) + d48502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27408 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (-2 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare27409 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (-2 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27410 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27408 p hg
    simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27411 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27412 (p : Pattern) (guard : d16 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27410 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27413 (p : Pattern) (guard : d17 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27412 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27414 (p : Pattern) (guard : d18 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27413 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27415 (p : Pattern) (guard : d19 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27414 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27416 (p : Pattern) (guard : d20 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27415 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27417 (p : Pattern) (guard : d21 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27416 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27418 (p : Pattern) (guard : d22 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27417 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27419 (p : Pattern) (guard : d0 p = 1) : d47631 p ≤ (-2 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27420 (p : Pattern) (guard : d23 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27418 p hg
    simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27421 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27422 (p : Pattern) (guard : d24 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27420 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27423 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (-2 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27424 (p : Pattern) (guard : d25 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27422 p hg
    simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27425 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (-2 : Int) + d47682 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27426 (p : Pattern) (guard : d26 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27424 p hg
    simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27427 (p : Pattern) (guard : d27 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27426 p hg
    simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27428 (p : Pattern) (guard : d0 p = 1) : d48700 p ≤ (-2 : Int) + d48502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27429 (p : Pattern) (guard : d28 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27427 p hg
    simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27430 (p : Pattern) (guard : d0 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27431 (p : Pattern) (guard : d29 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27429 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27432 (p : Pattern) (guard : d30 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27431 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27433 (p : Pattern) (guard : d31 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27432 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27434 (p : Pattern) (guard : d32 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27433 p hg
    simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27435 (p : Pattern) (guard : d33 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27434 p hg
    simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27436 (p : Pattern) (guard : d0 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27437 (p : Pattern) (guard : d34 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27435 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27438 (p : Pattern) (guard : d35 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27439 (p : Pattern) (guard : d0 p = 1) : d48600 p ≤ (-2 : Int) + d48498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27440 (p : Pattern) (guard : d14 p = 1) : d0 p ≤ (-2 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare27441 (p : Pattern) (guard : d0 p = 1) : d47612 p ≤ (-2 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27442 (p : Pattern) (guard : d15 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27440 p hg
    simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27441 p hg
    simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27443 (p : Pattern) (guard : d0 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27444 (p : Pattern) (guard : d16 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27442 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27445 (p : Pattern) (guard : d17 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27444 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27446 (p : Pattern) (guard : d18 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27445 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27447 (p : Pattern) (guard : d19 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27446 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27448 (p : Pattern) (guard : d20 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27447 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27449 (p : Pattern) (guard : d21 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27448 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27450 (p : Pattern) (guard : d22 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27449 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27451 (p : Pattern) (guard : d0 p = 1) : d47614 p ≤ (-2 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27452 (p : Pattern) (guard : d23 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27450 p hg
    simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27453 (p : Pattern) (guard : d0 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27454 (p : Pattern) (guard : d24 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27452 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27455 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-2 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27456 (p : Pattern) (guard : d25 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27454 p hg
    simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27457 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (-2 : Int) + d47793 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27458 (p : Pattern) (guard : d26 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27456 p hg
    simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27459 (p : Pattern) (guard : d27 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27458 p hg
    simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27460 (p : Pattern) (guard : d0 p = 1) : d48568 p ≤ (-2 : Int) + d48498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27461 (p : Pattern) (guard : d28 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27459 p hg
    simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27462 (p : Pattern) (guard : d29 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27461 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27463 (p : Pattern) (guard : d30 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27462 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27464 (p : Pattern) (guard : d31 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27463 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27465 (p : Pattern) (guard : d18544 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d31 p = 1 := by simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27464 p hg
    simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27466 (p : Pattern) (guard : d18545 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18544 p = 1 := by simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27465 p hg
    simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27467 (p : Pattern) (guard : d18546 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18545 p = 1 := by simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27466 p hg
    simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27468 (p : Pattern) (guard : d18547 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18546 p = 1 := by simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27467 p hg
    simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27469 (p : Pattern) (guard : d187879 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27438 p hg
    simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18547 p = 1 := by simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27468 p hg
    simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27470 (p : Pattern) (guard : d0 p = 1) : d48704 p ≤ (-2 : Int) + d188505 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27471 (p : Pattern) (guard : d187880 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187879 p = 1 := by simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27469 p hg
    simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27472 (p : Pattern) (guard : d187881 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187880 p = 1 := by simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27471 p hg
    simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27473 (p : Pattern) (guard : d187882 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187881 p = 1 := by simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27472 p hg
    simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27474 (p : Pattern) (guard : d187883 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187882 p = 1 := by simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27473 p hg
    simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27475 (p : Pattern) (guard : d187884 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187883 p = 1 := by simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27474 p hg
    simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27476 (p : Pattern) (guard : d187885 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187884 p = 1 := by simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27475 p hg
    simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27477 (p : Pattern) (guard : d187886 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187885 p = 1 := by simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27476 p hg
    simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27478 (p : Pattern) (guard : d187946 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187886 p = 1 := by simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27477 p hg
    simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27479 (p : Pattern) (guard : d187947 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d187946 p = 1 := by simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27478 p hg
    simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27480 (p : Pattern) (guard : d187948 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187947 p = 1 := by simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27479 p hg
    simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27481 (p : Pattern) (guard : d187949 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187948 p = 1 := by simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27480 p hg
    simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27482 (p : Pattern) (guard : d187950 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187949 p = 1 := by simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27481 p hg
    simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27483 (p : Pattern) (guard : d187951 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187950 p = 1 := by simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27482 p hg
    simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27484 (p : Pattern) (guard : d188290 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d187951 p = 1 := by simpa only [d188290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27483 p hg
    simpa only [d188290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27485 (p : Pattern) (guard : d188291 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188290 p = 1 := by simpa only [d188291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27484 p hg
    simpa only [d188291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27486 (p : Pattern) (guard : d188292 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188291 p = 1 := by simpa only [d188292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27485 p hg
    simpa only [d188292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27487 (p : Pattern) (guard : d0 p = 1) : d48747 p ≤ (-2 : Int) + d188516 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27488 (p : Pattern) (guard : d188293 p = 1) : d48748 p ≤ (-2 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188292 p = 1 := by simpa only [d188293, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27486 p hg
    simpa only [d188293, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188293, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d188293, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27489 (p : Pattern) (guard : d188294 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188294, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d188294, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188293 p = 1 := by simpa only [d188294, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27488 p hg
    simpa only [d188294, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27490 (p : Pattern) (guard : d188295 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188294 p = 1 := by simpa only [d188295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27489 p hg
    simpa only [d188295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27491 (p : Pattern) (guard : d188296 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188295 p = 1 := by simpa only [d188296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27490 p hg
    simpa only [d188296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27492 (p : Pattern) (guard : d188297 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188296 p = 1 := by simpa only [d188297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27491 p hg
    simpa only [d188297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27493 (p : Pattern) (guard : d188298 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188297 p = 1 := by simpa only [d188298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27492 p hg
    simpa only [d188298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27494 (p : Pattern) (guard : d188299 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188298 p = 1 := by simpa only [d188299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27493 p hg
    simpa only [d188299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27495 (p : Pattern) (guard : d128 p = 1) : d2 p ≤ (-2 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare27496 (p : Pattern) (guard : d13 p = 1) : d2 p ≤ (-2 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare27497 (p : Pattern) (guard : d14 p = 1) : d47629 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27496 p hg
    simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27498 (p : Pattern) (guard : d129 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27495 p hg
    simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27497 p hg
    simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27499 (p : Pattern) (guard : d130 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27498 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27410 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
