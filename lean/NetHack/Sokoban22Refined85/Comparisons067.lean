/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9380 (p : Pattern) (guard : d0 p = 1) : d1220 p ≤ (0 : Int) + d397 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9381 (p : Pattern) (guard : d4303 p = 1) : d1221 p ≤ (0 : Int) + d660 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1221, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9379 p hg
    simpa only [d4303, d1221, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1221, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9380 p hg
    simpa only [d4303, d1221, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9382 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9383 (p : Pattern) (guard : d4148 p = 1) : d1193 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9382 p hg
    simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9384 (p : Pattern) (guard : d4148 p = 1) : d1222 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1222, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9383 p hg
    simpa only [d1222, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1222, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d1222, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9385 (p : Pattern) (guard : d4148 p = 1) : d1223 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1223, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9384 p hg
    simpa only [d1223, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1223, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1223, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9386 (p : Pattern) (guard : d4148 p = 1) : d1224 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1224, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9385 p hg
    simpa only [d1224, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1224, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d1224, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9387 (p : Pattern) (guard : d0 p = 1) : d1227 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9388 (p : Pattern) (guard : d4303 p = 1) : d1228 p ≤ (0 : Int) + d661 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1228, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9386 p hg
    simpa only [d4303, d1228, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1228, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9387 p hg
    simpa only [d4303, d1228, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9389 (p : Pattern) (guard : d4303 p = 1) : d1229 p ≤ (0 : Int) + d662 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1229, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9381 p hg
    simpa only [d1229, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1229, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9388 p hg
    simpa only [d1229, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9390 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9391 (p : Pattern) (guard : d4148 p = 1) : d1185 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9390 p hg
    simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9392 (p : Pattern) (guard : d4148 p = 1) : d1230 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1230, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9391 p hg
    simpa only [d1230, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1230, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d1230, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9393 (p : Pattern) (guard : d4148 p = 1) : d1231 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1231, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9392 p hg
    simpa only [d1231, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1231, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1231, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9394 (p : Pattern) (guard : d4148 p = 1) : d1232 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1232, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9393 p hg
    simpa only [d1232, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1232, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d1232, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9395 (p : Pattern) (guard : d0 p = 1) : d1227 p ≤ (0 : Int) + d410 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9396 (p : Pattern) (guard : d4303 p = 1) : d1233 p ≤ (0 : Int) + d663 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1233, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9394 p hg
    simpa only [d4303, d1233, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1233, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9395 p hg
    simpa only [d4303, d1233, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9397 (p : Pattern) (guard : d4303 p = 1) : d1234 p ≤ (0 : Int) + d664 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1234, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9396 p hg
    simpa only [d1234, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1234, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1234, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9398 (p : Pattern) (guard : d4303 p = 1) : d1235 p ≤ (0 : Int) + d665 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1235, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9389 p hg
    simpa only [d1235, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1235, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9397 p hg
    simpa only [d1235, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9399 (p : Pattern) (guard : d4303 p = 1) : d1236 p ≤ (0 : Int) + d666 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1236, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9367 p hg
    simpa only [d1236, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1236, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9398 p hg
    simpa only [d1236, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9400 (p : Pattern) (guard : d0 p = 1) : d344 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9401 (p : Pattern) (guard : d4148 p = 1) : d1237 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9400 p hg
    simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9402 (p : Pattern) (guard : d4148 p = 1) : d1238 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1238, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9401 p hg
    simpa only [d1238, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1238, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9324 p hg
    simpa only [d1238, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9403 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9404 (p : Pattern) (guard : d4148 p = 1) : d1197 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1197, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1197, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1197, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9403 p hg
    simpa only [d4148, d1197, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9405 (p : Pattern) (guard : d4148 p = 1) : d1239 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1239, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9404 p hg
    simpa only [d1239, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1239, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1239, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9406 (p : Pattern) (guard : d4148 p = 1) : d1240 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1240, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9402 p hg
    simpa only [d1240, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1240, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9405 p hg
    simpa only [d1240, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9407 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9408 (p : Pattern) (guard : d4148 p = 1) : d1241 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1241, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1241, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1241, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9407 p hg
    simpa only [d4148, d1241, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9409 (p : Pattern) (guard : d4148 p = 1) : d1242 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1242, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9408 p hg
    simpa only [d1242, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1242, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d1242, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9410 (p : Pattern) (guard : d4148 p = 1) : d1243 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1243, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9409 p hg
    simpa only [d1243, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1243, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1243, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9411 (p : Pattern) (guard : d4148 p = 1) : d1244 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1244, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9406 p hg
    simpa only [d1244, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1244, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9410 p hg
    simpa only [d1244, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9412 (p : Pattern) (guard : d0 p = 1) : d1248 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9413 (p : Pattern) (guard : d4303 p = 1) : d1249 p ≤ (0 : Int) + d667 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1249, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9411 p hg
    simpa only [d4303, d1249, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1249, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9412 p hg
    simpa only [d4303, d1249, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9414 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9415 (p : Pattern) (guard : d4148 p = 1) : d1197 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9414 p hg
    simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9416 (p : Pattern) (guard : d4148 p = 1) : d1250 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1250, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9415 p hg
    simpa only [d1250, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1250, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d1250, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9417 (p : Pattern) (guard : d4148 p = 1) : d1251 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1251, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9416 p hg
    simpa only [d1251, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1251, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1251, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9418 (p : Pattern) (guard : d4148 p = 1) : d1252 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1252, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9417 p hg
    simpa only [d1252, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1252, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d1252, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9419 (p : Pattern) (guard : d0 p = 1) : d1255 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9420 (p : Pattern) (guard : d4303 p = 1) : d1256 p ≤ (0 : Int) + d668 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1256, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9418 p hg
    simpa only [d4303, d1256, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1256, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9419 p hg
    simpa only [d4303, d1256, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9421 (p : Pattern) (guard : d4303 p = 1) : d1257 p ≤ (0 : Int) + d669 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1257, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9413 p hg
    simpa only [d1257, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1257, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9420 p hg
    simpa only [d1257, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9422 (p : Pattern) (guard : d4303 p = 1) : d1205 p ≤ (0 : Int) + d670 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1205, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9364 p hg
    simpa only [d4303, d1205, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1205, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2260 p hg
    simpa only [d4303, d1205, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9423 (p : Pattern) (guard : d4303 p = 1) : d1258 p ≤ (0 : Int) + d671 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1258, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9350 p hg
    simpa only [d1258, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1258, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9422 p hg
    simpa only [d1258, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9424 (p : Pattern) (guard : d4303 p = 1) : d1259 p ≤ (0 : Int) + d672 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1259, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9421 p hg
    simpa only [d1259, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1259, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9423 p hg
    simpa only [d1259, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9425 (p : Pattern) (guard : d4148 p = 1) : d1260 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1260, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9357 p hg
    simpa only [d1260, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1260, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9378 p hg
    simpa only [d1260, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9426 (p : Pattern) (guard : d0 p = 1) : d1261 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9427 (p : Pattern) (guard : d4303 p = 1) : d1262 p ≤ (0 : Int) + d673 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1262, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9425 p hg
    simpa only [d4303, d1262, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1262, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9426 p hg
    simpa only [d4303, d1262, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9428 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9429 (p : Pattern) (guard : d4148 p = 1) : d1177 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9428 p hg
    simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9430 (p : Pattern) (guard : d4148 p = 1) : d1177 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9429 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9431 (p : Pattern) (guard : d4148 p = 1) : d1263 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1263, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9430 p hg
    simpa only [d1263, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1263, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1263, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9432 (p : Pattern) (guard : d4148 p = 1) : d1264 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1264, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9431 p hg
    simpa only [d1264, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1264, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d1264, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9433 (p : Pattern) (guard : d0 p = 1) : d1227 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9434 (p : Pattern) (guard : d4303 p = 1) : d1265 p ≤ (0 : Int) + d674 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1265, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9432 p hg
    simpa only [d4303, d1265, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1265, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9433 p hg
    simpa only [d4303, d1265, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9435 (p : Pattern) (guard : d4303 p = 1) : d1266 p ≤ (0 : Int) + d675 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1266, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9427 p hg
    simpa only [d1266, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1266, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9434 p hg
    simpa only [d1266, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9436 (p : Pattern) (guard : d4303 p = 1) : d1267 p ≤ (0 : Int) + d676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1267, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9388 p hg
    simpa only [d1267, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1267, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1267, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9437 (p : Pattern) (guard : d4303 p = 1) : d1268 p ≤ (0 : Int) + d677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1268, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9435 p hg
    simpa only [d1268, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1268, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9436 p hg
    simpa only [d1268, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9438 (p : Pattern) (guard : d4303 p = 1) : d1269 p ≤ (0 : Int) + d678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1269, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9424 p hg
    simpa only [d1269, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1269, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9437 p hg
    simpa only [d1269, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9439 (p : Pattern) (guard : d4303 p = 1) : d1270 p ≤ (0 : Int) + d679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1270, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9399 p hg
    simpa only [d1270, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1270, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9438 p hg
    simpa only [d1270, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9440 (p : Pattern) (guard : d0 p = 1) : d344 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9441 (p : Pattern) (guard : d4148 p = 1) : d1271 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9440 p hg
    simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9442 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9443 (p : Pattern) (guard : d4148 p = 1) : d1272 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1272, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1272, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1272, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9442 p hg
    simpa only [d4148, d1272, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9444 (p : Pattern) (guard : d4148 p = 1) : d1273 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1273, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9441 p hg
    simpa only [d1273, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1273, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9443 p hg
    simpa only [d1273, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9445 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9446 (p : Pattern) (guard : d4148 p = 1) : d1274 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1274, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1274, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1274, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9445 p hg
    simpa only [d4148, d1274, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9447 (p : Pattern) (guard : d4148 p = 1) : d1275 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1275, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9446 p hg
    simpa only [d1275, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1275, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1275, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9448 (p : Pattern) (guard : d4148 p = 1) : d1276 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1276, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9444 p hg
    simpa only [d1276, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1276, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9447 p hg
    simpa only [d1276, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9449 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9450 (p : Pattern) (guard : d4148 p = 1) : d1277 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1277, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d1277, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1277, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9449 p hg
    simpa only [d4148, d1277, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9451 (p : Pattern) (guard : d4148 p = 1) : d1278 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1278, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3760 p hg
    simpa only [d4148, d1278, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1278, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d4148, d1278, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9452 (p : Pattern) (guard : d4148 p = 1) : d1279 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1279, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9450 p hg
    simpa only [d1279, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1279, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1279, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9453 (p : Pattern) (guard : d4148 p = 1) : d1280 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1280, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1280, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1280, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d1280, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9454 (p : Pattern) (guard : d4148 p = 1) : d1281 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1281, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9452 p hg
    simpa only [d1281, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1281, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1281, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9455 (p : Pattern) (guard : d4148 p = 1) : d1282 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1282, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9448 p hg
    simpa only [d1282, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1282, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9454 p hg
    simpa only [d1282, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9456 (p : Pattern) (guard : d0 p = 1) : d1294 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9457 (p : Pattern) (guard : d4303 p = 1) : d1295 p ≤ (0 : Int) + d680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1295, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9455 p hg
    simpa only [d4303, d1295, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1295, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9456 p hg
    simpa only [d4303, d1295, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9458 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9459 (p : Pattern) (guard : d4148 p = 1) : d1274 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9458 p hg
    simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9460 (p : Pattern) (guard : d4148 p = 1) : d1296 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1296, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1296, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1296, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d4148, d1296, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9461 (p : Pattern) (guard : d4148 p = 1) : d1297 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1297, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9459 p hg
    simpa only [d1297, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1297, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1297, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9462 (p : Pattern) (guard : d4148 p = 1) : d1298 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1298, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1298, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1298, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1298, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9463 (p : Pattern) (guard : d4148 p = 1) : d1299 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1299, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9461 p hg
    simpa only [d1299, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1299, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1299, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9464 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2394 p hg
    simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9465 (p : Pattern) (guard : d4148 p = 1) : d1300 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9464 p hg
    simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9466 (p : Pattern) (guard : d4148 p = 1) : d1301 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9465 p hg
    simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9467 (p : Pattern) (guard : d4148 p = 1) : d1302 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1302, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9463 p hg
    simpa only [d1302, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1302, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1302, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9468 (p : Pattern) (guard : d0 p = 1) : d1306 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9469 (p : Pattern) (guard : d4303 p = 1) : d1307 p ≤ (0 : Int) + d681 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1307, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9467 p hg
    simpa only [d4303, d1307, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1307, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9468 p hg
    simpa only [d4303, d1307, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9470 (p : Pattern) (guard : d4303 p = 1) : d1308 p ≤ (0 : Int) + d682 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1308, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9457 p hg
    simpa only [d1308, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1308, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9469 p hg
    simpa only [d1308, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9471 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9472 (p : Pattern) (guard : d4148 p = 1) : d1272 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9471 p hg
    simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9473 (p : Pattern) (guard : d4148 p = 1) : d1309 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1309, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9472 p hg
    simpa only [d1309, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1309, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1309, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9474 (p : Pattern) (guard : d4148 p = 1) : d1310 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1310, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9473 p hg
    simpa only [d1310, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1310, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1310, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9475 (p : Pattern) (guard : d4148 p = 1) : d1311 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1311, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9474 p hg
    simpa only [d1311, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1311, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1311, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9476 (p : Pattern) (guard : d0 p = 1) : d1315 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9477 (p : Pattern) (guard : d4303 p = 1) : d1316 p ≤ (0 : Int) + d683 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1316, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9475 p hg
    simpa only [d4303, d1316, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1316, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9476 p hg
    simpa only [d4303, d1316, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9478 (p : Pattern) (guard : d4303 p = 1) : d1317 p ≤ (0 : Int) + d684 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1317, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9477 p hg
    simpa only [d1317, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1317, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d1317, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9479 (p : Pattern) (guard : d4303 p = 1) : d1318 p ≤ (0 : Int) + d685 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1318, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9470 p hg
    simpa only [d1318, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1318, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9478 p hg
    simpa only [d1318, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9480 (p : Pattern) (guard : d0 p = 1) : d345 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9481 (p : Pattern) (guard : d4148 p = 1) : d1319 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9480 p hg
    simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9482 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9483 (p : Pattern) (guard : d4148 p = 1) : d1303 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1303, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1303, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1303, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9482 p hg
    simpa only [d4148, d1303, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9484 (p : Pattern) (guard : d4148 p = 1) : d1320 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1320, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9481 p hg
    simpa only [d1320, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1320, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9483 p hg
    simpa only [d1320, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9485 (p : Pattern) (guard : d4148 p = 1) : d1321 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1321, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9484 p hg
    simpa only [d1321, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1321, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1321, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9486 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9487 (p : Pattern) (guard : d4148 p = 1) : d1322 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1322, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d1322, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1322, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d4148, d1322, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9488 (p : Pattern) (guard : d4148 p = 1) : d1323 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1323, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9487 p hg
    simpa only [d1323, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1323, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1323, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9489 (p : Pattern) (guard : d4148 p = 1) : d1324 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1324, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9488 p hg
    simpa only [d1324, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1324, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1324, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9490 (p : Pattern) (guard : d4148 p = 1) : d1325 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1325, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9485 p hg
    simpa only [d1325, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1325, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9489 p hg
    simpa only [d1325, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9491 (p : Pattern) (guard : d0 p = 1) : d1328 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9492 (p : Pattern) (guard : d4303 p = 1) : d1329 p ≤ (0 : Int) + d686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1329, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d4303, d1329, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1329, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9491 p hg
    simpa only [d4303, d1329, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9493 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9494 (p : Pattern) (guard : d4148 p = 1) : d1296 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9493 p hg
    simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9495 (p : Pattern) (guard : d4148 p = 1) : d1296 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9496 (p : Pattern) (guard : d4148 p = 1) : d1330 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1330, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9495 p hg
    simpa only [d1330, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1330, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1330, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9497 (p : Pattern) (guard : d4148 p = 1) : d1331 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1331, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9496 p hg
    simpa only [d1331, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1331, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1331, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9498 (p : Pattern) (guard : d0 p = 1) : d1334 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9499 (p : Pattern) (guard : d4303 p = 1) : d1335 p ≤ (0 : Int) + d687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1335, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9497 p hg
    simpa only [d4303, d1335, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1335, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9498 p hg
    simpa only [d4303, d1335, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9500 (p : Pattern) (guard : d4303 p = 1) : d1336 p ≤ (0 : Int) + d688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1336, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9492 p hg
    simpa only [d1336, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1336, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9499 p hg
    simpa only [d1336, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9501 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9502 (p : Pattern) (guard : d4148 p = 1) : d1303 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9501 p hg
    simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9503 (p : Pattern) (guard : d4148 p = 1) : d1337 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1337, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9502 p hg
    simpa only [d1337, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1337, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1337, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9504 (p : Pattern) (guard : d4148 p = 1) : d1338 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1338, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9503 p hg
    simpa only [d1338, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1338, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1338, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9505 (p : Pattern) (guard : d4148 p = 1) : d1339 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9504 p hg
    simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9506 (p : Pattern) (guard : d0 p = 1) : d1334 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9507 (p : Pattern) (guard : d4303 p = 1) : d1340 p ≤ (0 : Int) + d689 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1340, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d4303, d1340, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1340, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9506 p hg
    simpa only [d4303, d1340, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9508 (p : Pattern) (guard : d4303 p = 1) : d1341 p ≤ (0 : Int) + d690 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1341, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9507 p hg
    simpa only [d1341, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1341, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1341, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9509 (p : Pattern) (guard : d4303 p = 1) : d1342 p ≤ (0 : Int) + d691 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1342, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9500 p hg
    simpa only [d1342, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1342, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9508 p hg
    simpa only [d1342, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9510 (p : Pattern) (guard : d4303 p = 1) : d1343 p ≤ (0 : Int) + d692 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1343, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9479 p hg
    simpa only [d1343, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1343, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9509 p hg
    simpa only [d1343, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9511 (p : Pattern) (guard : d4303 p = 1) : d1344 p ≤ (0 : Int) + d693 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1344, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9399 p hg
    simpa only [d1344, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1344, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9510 p hg
    simpa only [d1344, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9512 (p : Pattern) (guard : d4303 p = 1) : d1345 p ≤ (0 : Int) + d694 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1345, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9439 p hg
    simpa only [d1345, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1345, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9511 p hg
    simpa only [d1345, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9513 (p : Pattern) (guard : d0 p = 1) : d1350 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9514 (p : Pattern) (guard : d4303 p = 1) : d1351 p ≤ (0 : Int) + d674 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1351, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9432 p hg
    simpa only [d4303, d1351, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1351, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9513 p hg
    simpa only [d4303, d1351, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9515 (p : Pattern) (guard : d4303 p = 1) : d1352 p ≤ (0 : Int) + d675 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1352, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9427 p hg
    simpa only [d1352, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1352, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9514 p hg
    simpa only [d1352, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9516 (p : Pattern) (guard : d0 p = 1) : d1350 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9517 (p : Pattern) (guard : d4303 p = 1) : d1353 p ≤ (0 : Int) + d661 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1353, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9386 p hg
    simpa only [d4303, d1353, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1353, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9516 p hg
    simpa only [d4303, d1353, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9518 (p : Pattern) (guard : d4303 p = 1) : d1354 p ≤ (0 : Int) + d676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1354, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9517 p hg
    simpa only [d1354, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1354, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1354, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9519 (p : Pattern) (guard : d4303 p = 1) : d1355 p ≤ (0 : Int) + d677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1355, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9515 p hg
    simpa only [d1355, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1355, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9518 p hg
    simpa only [d1355, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
