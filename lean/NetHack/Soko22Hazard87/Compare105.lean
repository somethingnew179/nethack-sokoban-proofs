import NetHack.Soko22Hazard87.Compare104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26250 (p : Pattern) (guard : d1205 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26249 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26251 (p : Pattern) (guard : d1206 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26250 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25966 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26252 (p : Pattern) (guard : d1207 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26247 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26251 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26253 (p : Pattern) (guard : d1208 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26252 p hg
    simpa only [d1208, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1208, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26254 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (-1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26255 (p : Pattern) (guard : d1084 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26254 p hg
    simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25577 p hg
    simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26256 (p : Pattern) (guard : d1085 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26255 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26257 (p : Pattern) (guard : d1086 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26256 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26258 (p : Pattern) (guard : d1087 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26257 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26259 (p : Pattern) (guard : d1088 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25777 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26258 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26260 (p : Pattern) (guard : d1089 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26259 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26261 (p : Pattern) (guard : d1090 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25960 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26260 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26262 (p : Pattern) (guard : d1091 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26261 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25967 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26263 (p : Pattern) (guard : d1092 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26262 p hg
    simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26264 (p : Pattern) (guard : d1209 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26253 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26263 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26265 (p : Pattern) (guard : d1210 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26264 p hg
    simpa only [d1210, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1210, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26266 (p : Pattern) (guard : d1211 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26265 p hg
    simpa only [d1211, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1211, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26267 (p : Pattern) (guard : d1212 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1212, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1212, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1212, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26266 p hg
    simpa only [d1212, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26268 (p : Pattern) (guard : d1213 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26267 p hg
    simpa only [d1213, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1213, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26269 (p : Pattern) (guard : d9749 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25982 p hg
    simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26270 (p : Pattern) (guard : d9750 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9749 p = 1 := by simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26269 p hg
    simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26271 (p : Pattern) (guard : d9751 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9750 p = 1 := by simpa only [d9751, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26270 p hg
    simpa only [d9751, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9751, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9751, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26272 (p : Pattern) (guard : d9752 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26263 p hg
    simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9751 p = 1 := by simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26271 p hg
    simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26273 (p : Pattern) (guard : d9753 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9752 p = 1 := by simpa only [d9753, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26272 p hg
    simpa only [d9753, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9753, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9753, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26274 (p : Pattern) (guard : d9755 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9753 p = 1 := by simpa only [d9755, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26273 p hg
    simpa only [d9755, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9755, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9755, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26275 (p : Pattern) (guard : d16507 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16507, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d16507, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9755 p = 1 := by simpa only [d16507, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26274 p hg
    simpa only [d16507, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26276 (p : Pattern) (guard : d16508 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16507 p = 1 := by simpa only [d16508, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26275 p hg
    simpa only [d16508, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16508, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d16508, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26277 (p : Pattern) (guard : d16509 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26268 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16508 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26276 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26278 (p : Pattern) (guard : d9759 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25960 p hg
    simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26279 (p : Pattern) (guard : d9760 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9759 p = 1 := by simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26278 p hg
    simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26280 (p : Pattern) (guard : d9761 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9760 p = 1 := by simpa only [d9761, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26279 p hg
    simpa only [d9761, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9761, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9761, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26281 (p : Pattern) (guard : d9762 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9761 p = 1 := by simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26280 p hg
    simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9751 p = 1 := by simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26271 p hg
    simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26282 (p : Pattern) (guard : d9763 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9762 p = 1 := by simpa only [d9763, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26281 p hg
    simpa only [d9763, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9763, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9763, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26283 (p : Pattern) (guard : d9765 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9763 p = 1 := by simpa only [d9765, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26282 p hg
    simpa only [d9765, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9765, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9765, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26284 (p : Pattern) (guard : d14836 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d14836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9765 p = 1 := by simpa only [d14836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26283 p hg
    simpa only [d14836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26285 (p : Pattern) (guard : d14837 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14836 p = 1 := by simpa only [d14837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26284 p hg
    simpa only [d14837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d14837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26286 (p : Pattern) (guard : d9768 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26260 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25982 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26287 (p : Pattern) (guard : d9769 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9768 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26286 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26288 (p : Pattern) (guard : d9770 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9769 p = 1 := by simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26287 p hg
    simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26289 (p : Pattern) (guard : d9771 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26257 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26290 (p : Pattern) (guard : d9772 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25980 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26289 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26291 (p : Pattern) (guard : d9773 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9772 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26290 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26292 (p : Pattern) (guard : d9774 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9773 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26291 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25797 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26293 (p : Pattern) (guard : d9775 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9774 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26292 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26294 (p : Pattern) (guard : d9776 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9775 p = 1 := by simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26293 p hg
    simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26295 (p : Pattern) (guard : d9777 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9770 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26288 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26294 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26296 (p : Pattern) (guard : d9778 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26295 p hg
    simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26297 (p : Pattern) (guard : d9780 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26296 p hg
    simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26298 (p : Pattern) (guard : d14758 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26297 p hg
    simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26299 (p : Pattern) (guard : d14759 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26298 p hg
    simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26300 (p : Pattern) (guard : d16510 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14837 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26285 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14759 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26299 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26301 (p : Pattern) (guard : d16511 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16509 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26277 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16510 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26300 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26302 (p : Pattern) (guard : d1093 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26257 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25502 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26303 (p : Pattern) (guard : d1094 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25661 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26302 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26304 (p : Pattern) (guard : d1095 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26303 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26305 (p : Pattern) (guard : d1096 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26260 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26304 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26306 (p : Pattern) (guard : d1097 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26305 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25786 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26307 (p : Pattern) (guard : d1098 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26306 p hg
    simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26308 (p : Pattern) (guard : d1099 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26263 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26307 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26309 (p : Pattern) (guard : d1100 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26308 p hg
    simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26310 (p : Pattern) (guard : d1101 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26309 p hg
    simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26311 (p : Pattern) (guard : d1102 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26310 p hg
    simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26312 (p : Pattern) (guard : d1103 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26311 p hg
    simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26313 (p : Pattern) (guard : d9788 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26307 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26294 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26314 (p : Pattern) (guard : d9789 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26313 p hg
    simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26315 (p : Pattern) (guard : d9791 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26314 p hg
    simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26316 (p : Pattern) (guard : d16438 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26315 p hg
    simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26317 (p : Pattern) (guard : d16439 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26316 p hg
    simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26318 (p : Pattern) (guard : d16440 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26312 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26317 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26319 (p : Pattern) (guard : d9795 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26304 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25797 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26320 (p : Pattern) (guard : d9796 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25583 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26321 (p : Pattern) (guard : d9797 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26319 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26320 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26322 (p : Pattern) (guard : d9798 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26321 p hg
    simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26323 (p : Pattern) (guard : d1115 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25503 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26324 (p : Pattern) (guard : d1116 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26323 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26325 (p : Pattern) (guard : d1117 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26324 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25505 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26326 (p : Pattern) (guard : d1118 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26325 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25506 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26327 (p : Pattern) (guard : d1119 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26326 p hg
    simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26328 (p : Pattern) (guard : d9799 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26322 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26327 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26329 (p : Pattern) (guard : d9800 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26328 p hg
    simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26330 (p : Pattern) (guard : d9802 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26329 p hg
    simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26331 (p : Pattern) (guard : d14763 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26330 p hg
    simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26332 (p : Pattern) (guard : d14764 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26331 p hg
    simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26333 (p : Pattern) (guard : d16441 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26299 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26332 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26334 (p : Pattern) (guard : d16442 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26318 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26335 (p : Pattern) (guard : d16512 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16511 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26301 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16442 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26336 (p : Pattern) (guard : d19056 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16512 p = 1 := by simpa only [d19056, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d19056, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19056, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19056, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26337 (p : Pattern) (guard : d19057 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19057, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19057, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19056 p = 1 := by simpa only [d19057, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26336 p hg
    simpa only [d19057, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26338 (p : Pattern) (guard : d9810 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26260 p hg
    simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9773 p = 1 := by simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26291 p hg
    simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26339 (p : Pattern) (guard : d9811 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9810 p = 1 := by simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26338 p hg
    simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26340 (p : Pattern) (guard : d9812 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9811 p = 1 := by simpa only [d9812, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26339 p hg
    simpa only [d9812, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9812, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9812, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26341 (p : Pattern) (guard : d9813 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9812 p = 1 := by simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26294 p hg
    simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26342 (p : Pattern) (guard : d9814 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9813 p = 1 := by simpa only [d9814, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26341 p hg
    simpa only [d9814, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9814, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9814, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26343 (p : Pattern) (guard : d9816 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9814 p = 1 := by simpa only [d9816, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26342 p hg
    simpa only [d9816, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9816, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9816, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26344 (p : Pattern) (guard : d13022 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13022, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d13022, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9816 p = 1 := by simpa only [d13022, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26343 p hg
    simpa only [d13022, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26345 (p : Pattern) (guard : d13023 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13022 p = 1 := by simpa only [d13023, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26344 p hg
    simpa only [d13023, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13023, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d13023, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26346 (p : Pattern) (guard : d16515 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13023 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26345 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26332 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26347 (p : Pattern) (guard : d14765 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26332 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26348 (p : Pattern) (guard : d16516 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16515 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26346 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26347 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26349 (p : Pattern) (guard : d16517 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16516 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26348 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26350 (p : Pattern) (guard : d19058 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16517 p = 1 := by simpa only [d19058, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26349 p hg
    simpa only [d19058, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19058, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19058, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26351 (p : Pattern) (guard : d19059 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19059, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19059, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19058 p = 1 := by simpa only [d19059, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26350 p hg
    simpa only [d19059, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26352 (p : Pattern) (guard : d19060 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19057 p = 1 := by simpa only [d19060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26337 p hg
    simpa only [d19060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19059 p = 1 := by simpa only [d19060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26351 p hg
    simpa only [d19060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26353 (p : Pattern) (guard : d1104 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25581 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25503 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26354 (p : Pattern) (guard : d1105 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26353 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26355 (p : Pattern) (guard : d1106 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26304 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26354 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26356 (p : Pattern) (guard : d1107 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25584 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26357 (p : Pattern) (guard : d1108 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26356 p hg
    simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26358 (p : Pattern) (guard : d1109 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26307 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26357 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26359 (p : Pattern) (guard : d1110 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26358 p hg
    simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26360 (p : Pattern) (guard : d1111 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26359 p hg
    simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26361 (p : Pattern) (guard : d1112 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26362 (p : Pattern) (guard : d1113 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26363 (p : Pattern) (guard : d1120 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26357 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26327 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26364 (p : Pattern) (guard : d1121 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26363 p hg
    simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26365 (p : Pattern) (guard : d1122 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26364 p hg
    simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26366 (p : Pattern) (guard : d1123 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26365 p hg
    simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26367 (p : Pattern) (guard : d1124 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26366 p hg
    simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26368 (p : Pattern) (guard : d1125 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26362 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26367 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26369 (p : Pattern) (guard : d16443 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26368 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26347 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26370 (p : Pattern) (guard : d16444 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26334 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26369 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26371 (p : Pattern) (guard : d19061 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16444 p = 1 := by simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26370 p hg
    simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26372 (p : Pattern) (guard : d19062 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19061 p = 1 := by simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26371 p hg
    simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26373 (p : Pattern) (guard : d5012 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25795 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25503 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26374 (p : Pattern) (guard : d5013 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26373 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26375 (p : Pattern) (guard : d5014 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26304 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26374 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26376 (p : Pattern) (guard : d5015 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26375 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25584 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26377 (p : Pattern) (guard : d5016 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26376 p hg
    simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26378 (p : Pattern) (guard : d5017 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26377 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26327 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26379 (p : Pattern) (guard : d5018 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26378 p hg
    simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26380 (p : Pattern) (guard : d5019 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26379 p hg
    simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26381 (p : Pattern) (guard : d5020 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26380 p hg
    simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26382 (p : Pattern) (guard : d5021 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26381 p hg
    simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26383 (p : Pattern) (guard : d5022 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26382 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26384 (p : Pattern) (guard : d1132 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26324 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26385 (p : Pattern) (guard : d9841 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26384 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25506 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26386 (p : Pattern) (guard : d9842 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9841 p = 1 := by simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26385 p hg
    simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26387 (p : Pattern) (guard : d9843 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9842 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26386 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26388 (p : Pattern) (guard : d9844 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26387 p hg
    simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26389 (p : Pattern) (guard : d9846 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26388 p hg
    simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26390 (p : Pattern) (guard : d14770 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26389 p hg
    simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26391 (p : Pattern) (guard : d14771 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26390 p hg
    simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26392 (p : Pattern) (guard : d14772 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26391 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26393 (p : Pattern) (guard : d14773 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26383 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26392 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26394 (p : Pattern) (guard : d16447 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26369 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26393 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26395 (p : Pattern) (guard : d19063 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16447 p = 1 := by simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26394 p hg
    simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26396 (p : Pattern) (guard : d19064 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19063 p = 1 := by simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26395 p hg
    simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26397 (p : Pattern) (guard : d19065 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19062 p = 1 := by simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26372 p hg
    simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19064 p = 1 := by simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26396 p hg
    simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26398 (p : Pattern) (guard : d19066 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19060 p = 1 := by simpa only [d19066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26352 p hg
    simpa only [d19066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19065 p = 1 := by simpa only [d19066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26397 p hg
    simpa only [d19066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26399 (p : Pattern) (guard : d188070 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16521 p = 1 := by simpa only [d188070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26243 p hg
    simpa only [d188070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19066 p = 1 := by simpa only [d188070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26398 p hg
    simpa only [d188070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26400 (p : Pattern) (guard : d188071 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188070 p = 1 := by simpa only [d188071, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26399 p hg
    simpa only [d188071, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188071, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188071, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26401 (p : Pattern) (guard : d188072 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188072, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188072, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188071 p = 1 := by simpa only [d188072, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26400 p hg
    simpa only [d188072, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26402 (p : Pattern) (guard : d16525 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16449 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26241 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26403 (p : Pattern) (guard : d16526 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26242 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16525 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26402 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26404 (p : Pattern) (guard : d19072 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19064 p = 1 := by simpa only [d19072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26396 p hg
    simpa only [d19072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26405 (p : Pattern) (guard : d19073 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19065 p = 1 := by simpa only [d19073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26397 p hg
    simpa only [d19073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19072 p = 1 := by simpa only [d19073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26404 p hg
    simpa only [d19073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26406 (p : Pattern) (guard : d188073 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16526 p = 1 := by simpa only [d188073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26403 p hg
    simpa only [d188073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19073 p = 1 := by simpa only [d188073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26405 p hg
    simpa only [d188073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26407 (p : Pattern) (guard : d188074 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188073 p = 1 := by simpa only [d188074, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26406 p hg
    simpa only [d188074, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188074, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188074, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26408 (p : Pattern) (guard : d188075 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188075, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188075, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188074 p = 1 := by simpa only [d188075, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26407 p hg
    simpa only [d188075, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26409 (p : Pattern) (guard : d188076 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188072 p = 1 := by simpa only [d188076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26401 p hg
    simpa only [d188076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188075 p = 1 := by simpa only [d188076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26408 p hg
    simpa only [d188076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26410 (p : Pattern) (guard : d188077 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188076 p = 1 := by simpa only [d188077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26409 p hg
    simpa only [d188077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26411 (p : Pattern) (guard : d188078 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188077 p = 1 := by simpa only [d188078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26410 p hg
    simpa only [d188078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26412 (p : Pattern) (guard : d188079 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188078 p = 1 := by simpa only [d188079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26411 p hg
    simpa only [d188079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26413 (p : Pattern) (guard : d1127 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26212 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26414 (p : Pattern) (guard : d14778 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26413 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26237 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26415 (p : Pattern) (guard : d16451 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26214 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26414 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26416 (p : Pattern) (guard : d16452 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26415 p hg
    simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26417 (p : Pattern) (guard : d16453 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26416 p hg
    simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26418 (p : Pattern) (guard : d16454 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26417 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26419 (p : Pattern) (guard : d16459 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26418 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26420 (p : Pattern) (guard : d1127 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26367 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26421 (p : Pattern) (guard : d14778 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26420 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26392 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26422 (p : Pattern) (guard : d16451 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26369 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26421 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26423 (p : Pattern) (guard : d19088 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16451 p = 1 := by simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26422 p hg
    simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26424 (p : Pattern) (guard : d19089 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19088 p = 1 := by simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26423 p hg
    simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26425 (p : Pattern) (guard : d19090 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19089 p = 1 := by simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26424 p hg
    simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26426 (p : Pattern) (guard : d19091 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19090 p = 1 := by simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26425 p hg
    simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26427 (p : Pattern) (guard : d188080 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26419 p hg
    simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19091 p = 1 := by simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26426 p hg
    simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26428 (p : Pattern) (guard : d188081 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188080 p = 1 := by simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26427 p hg
    simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26429 (p : Pattern) (guard : d188082 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188081 p = 1 := by simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26428 p hg
    simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26430 (p : Pattern) (guard : d188083 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188075 p = 1 := by simpa only [d188083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26408 p hg
    simpa only [d188083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188082 p = 1 := by simpa only [d188083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26429 p hg
    simpa only [d188083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26431 (p : Pattern) (guard : d188084 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188083 p = 1 := by simpa only [d188084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26430 p hg
    simpa only [d188084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26432 (p : Pattern) (guard : d188085 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188084 p = 1 := by simpa only [d188085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d188085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26433 (p : Pattern) (guard : d188086 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188085 p = 1 := by simpa only [d188086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26432 p hg
    simpa only [d188086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26434 (p : Pattern) (guard : d188087 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188079 p = 1 := by simpa only [d188087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26412 p hg
    simpa only [d188087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188086 p = 1 := by simpa only [d188087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26433 p hg
    simpa only [d188087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26435 (p : Pattern) (guard : d188088 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188087 p = 1 := by simpa only [d188088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26434 p hg
    simpa only [d188088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26436 (p : Pattern) (guard : d12961 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26413 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26437 (p : Pattern) (guard : d16574 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26214 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12961 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26436 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26438 (p : Pattern) (guard : d16575 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16575, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16575, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16574 p = 1 := by simpa only [d16575, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d16575, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26439 (p : Pattern) (guard : d16576 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16576, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16576, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16575 p = 1 := by simpa only [d16576, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26438 p hg
    simpa only [d16576, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26440 (p : Pattern) (guard : d16577 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16576 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26439 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26441 (p : Pattern) (guard : d16578 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26242 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16577 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26440 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26442 (p : Pattern) (guard : d12961 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26420 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26443 (p : Pattern) (guard : d16574 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26369 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12961 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26442 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26444 (p : Pattern) (guard : d19180 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16574 p = 1 := by simpa only [d19180, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26443 p hg
    simpa only [d19180, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19180, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19180, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26445 (p : Pattern) (guard : d19181 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19181, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19181, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19180 p = 1 := by simpa only [d19181, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26444 p hg
    simpa only [d19181, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26446 (p : Pattern) (guard : d19182 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19181 p = 1 := by simpa only [d19182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26445 p hg
    simpa only [d19182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26447 (p : Pattern) (guard : d19183 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19065 p = 1 := by simpa only [d19183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26397 p hg
    simpa only [d19183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19182 p = 1 := by simpa only [d19183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26446 p hg
    simpa only [d19183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26448 (p : Pattern) (guard : d188089 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16578 p = 1 := by simpa only [d188089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26441 p hg
    simpa only [d188089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19183 p = 1 := by simpa only [d188089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26447 p hg
    simpa only [d188089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26449 (p : Pattern) (guard : d188090 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188089 p = 1 := by simpa only [d188090, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d188090, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188090, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188090, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26450 (p : Pattern) (guard : d188091 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188091, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188091, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188090 p = 1 := by simpa only [d188091, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26449 p hg
    simpa only [d188091, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26451 (p : Pattern) (guard : d188092 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188091 p = 1 := by simpa only [d188092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26450 p hg
    simpa only [d188092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26452 (p : Pattern) (guard : d188093 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188092 p = 1 := by simpa only [d188093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26451 p hg
    simpa only [d188093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26453 (p : Pattern) (guard : d188094 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188093 p = 1 := by simpa only [d188094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26452 p hg
    simpa only [d188094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26454 (p : Pattern) (guard : d188095 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188094 p = 1 := by simpa only [d188095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d188095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26455 (p : Pattern) (guard : d188096 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188095 p = 1 := by simpa only [d188096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d188096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26456 (p : Pattern) (guard : d188097 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188096 p = 1 := by simpa only [d188097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26455 p hg
    simpa only [d188097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26457 (p : Pattern) (guard : d188098 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188088 p = 1 := by simpa only [d188098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26435 p hg
    simpa only [d188098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188097 p = 1 := by simpa only [d188098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26456 p hg
    simpa only [d188098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26458 (p : Pattern) (guard : d188099 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188098 p = 1 := by simpa only [d188099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26457 p hg
    simpa only [d188099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26459 (p : Pattern) (guard : d188100 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188099 p = 1 := by simpa only [d188100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26458 p hg
    simpa only [d188100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26460 (p : Pattern) (guard : d188101 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188101, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188101, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188100 p = 1 := by simpa only [d188101, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26459 p hg
    simpa only [d188101, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26461 (p : Pattern) (guard : d188102 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188101 p = 1 := by simpa only [d188102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26460 p hg
    simpa only [d188102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26462 (p : Pattern) (guard : d188103 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188082 p = 1 := by simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26429 p hg
    simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26463 (p : Pattern) (guard : d188104 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188103 p = 1 := by simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26462 p hg
    simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26464 (p : Pattern) (guard : d188105 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188104 p = 1 := by simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26463 p hg
    simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26465 (p : Pattern) (guard : d188106 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188105 p = 1 := by simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26464 p hg
    simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26466 (p : Pattern) (guard : d188107 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188106 p = 1 := by simpa only [d188107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26465 p hg
    simpa only [d188107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26467 (p : Pattern) (guard : d188108 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188107 p = 1 := by simpa only [d188108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26466 p hg
    simpa only [d188108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26468 (p : Pattern) (guard : d188109 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188108 p = 1 := by simpa only [d188109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26467 p hg
    simpa only [d188109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26469 (p : Pattern) (guard : d188110 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188109 p = 1 := by simpa only [d188110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26468 p hg
    simpa only [d188110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26470 (p : Pattern) (guard : d188111 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188110 p = 1 := by simpa only [d188111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26469 p hg
    simpa only [d188111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26471 (p : Pattern) (guard : d188112 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188112, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188112, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188111 p = 1 := by simpa only [d188112, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26470 p hg
    simpa only [d188112, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26472 (p : Pattern) (guard : d188113 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188112 p = 1 := by simpa only [d188113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26471 p hg
    simpa only [d188113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26473 (p : Pattern) (guard : d188114 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188102 p = 1 := by simpa only [d188114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26461 p hg
    simpa only [d188114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188113 p = 1 := by simpa only [d188114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26472 p hg
    simpa only [d188114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26474 (p : Pattern) (guard : d188115 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188114 p = 1 := by simpa only [d188115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26473 p hg
    simpa only [d188115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26475 (p : Pattern) (guard : d188116 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188115 p = 1 := by simpa only [d188116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26474 p hg
    simpa only [d188116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26476 (p : Pattern) (guard : d188117 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188116 p = 1 := by simpa only [d188117, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26475 p hg
    simpa only [d188117, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188117, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d188117, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26477 (p : Pattern) (guard : d188118 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188118, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d188118, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188117 p = 1 := by simpa only [d188118, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26476 p hg
    simpa only [d188118, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26478 (p : Pattern) (guard : d188119 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188118 p = 1 := by simpa only [d188119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26477 p hg
    simpa only [d188119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26479 (p : Pattern) (guard : d188120 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188119 p = 1 := by simpa only [d188120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26478 p hg
    simpa only [d188120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26480 (p : Pattern) (guard : d188121 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188120 p = 1 := by simpa only [d188121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26479 p hg
    simpa only [d188121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26481 (p : Pattern) (guard : d188122 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188121 p = 1 := by simpa only [d188122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26480 p hg
    simpa only [d188122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26482 (p : Pattern) (guard : d188123 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188122 p = 1 := by simpa only [d188123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26481 p hg
    simpa only [d188123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26483 (p : Pattern) (guard : d188124 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188123 p = 1 := by simpa only [d188124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26482 p hg
    simpa only [d188124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26484 (p : Pattern) (guard : d188125 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188124 p = 1 := by simpa only [d188125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26483 p hg
    simpa only [d188125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26485 (p : Pattern) (guard : d188126 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188125 p = 1 := by simpa only [d188126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26484 p hg
    simpa only [d188126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26486 (p : Pattern) (guard : d188127 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d188069 p = 1 := by simpa only [d188127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26088 p hg
    simpa only [d188127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188126 p = 1 := by simpa only [d188127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26485 p hg
    simpa only [d188127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26487 (p : Pattern) (guard : d1660 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1201 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26488 (p : Pattern) (guard : d1661 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1205 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26095 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26489 (p : Pattern) (guard : d1662 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1660 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26487 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1661 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26488 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26490 (p : Pattern) (guard : d1663 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1662 p = 1 := by simpa only [d1663, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26489 p hg
    simpa only [d1663, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1663, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1663, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26491 (p : Pattern) (guard : d1520 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25626 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25905 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26492 (p : Pattern) (guard : d1521 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25724 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26491 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26493 (p : Pattern) (guard : d1522 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25885 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26492 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26494 (p : Pattern) (guard : d1523 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26099 p hg
    simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25625 p hg
    simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26495 (p : Pattern) (guard : d1524 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26494 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26100 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26496 (p : Pattern) (guard : d1525 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26495 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26497 (p : Pattern) (guard : d1526 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26496 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26498 (p : Pattern) (guard : d1527 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26493 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26497 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26499 (p : Pattern) (guard : d1528 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26103 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
