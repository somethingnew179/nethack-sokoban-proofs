/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10360 (p : Pattern) (guard : d4673 p = 1) : d1169 p ≤ (0 : Int) + d796 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10358 p hg
    simpa only [d4673, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10359 p hg
    simpa only [d4673, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10361 (p : Pattern) (guard : d0 p = 1) : d1170 p ≤ (0 : Int) + d176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10362 (p : Pattern) (guard : d4672 p = 1) : d1172 p ≤ (0 : Int) + d176 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10361 p hg
    simpa only [d4672, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d4672, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10363 (p : Pattern) (guard : d0 p = 1) : d1173 p ≤ (0 : Int) + d176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10364 (p : Pattern) (guard : d4673 p = 1) : d1174 p ≤ (0 : Int) + d176 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10362 p hg
    simpa only [d4673, d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10363 p hg
    simpa only [d4673, d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10365 (p : Pattern) (guard : d4673 p = 1) : d1175 p ≤ (0 : Int) + d4819 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1175, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10360 p hg
    simpa only [d1175, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1175, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10364 p hg
    simpa only [d1175, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10366 (p : Pattern) (guard : d4673 p = 1) : d1176 p ≤ (0 : Int) + d4820 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1176, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10354 p hg
    simpa only [d1176, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1176, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10365 p hg
    simpa only [d1176, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10367 (p : Pattern) (guard : d0 p = 1) : d1154 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10368 (p : Pattern) (guard : d4672 p = 1) : d1178 p ≤ (0 : Int) + d54 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10367 p hg
    simpa only [d4672, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d4672, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10369 (p : Pattern) (guard : d0 p = 1) : d1179 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10370 (p : Pattern) (guard : d4673 p = 1) : d1180 p ≤ (0 : Int) + d54 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10368 p hg
    simpa only [d4673, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d4673, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10371 (p : Pattern) (guard : d4672 p = 1) : d1182 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d4672, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d4672, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10372 (p : Pattern) (guard : d4673 p = 1) : d1183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10371 p hg
    simpa only [d4673, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4673, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10373 (p : Pattern) (guard : d4673 p = 1) : d1184 p ≤ (0 : Int) + d4821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1184, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10370 p hg
    simpa only [d1184, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1184, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d1184, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10374 (p : Pattern) (guard : d0 p = 1) : d1185 p ≤ (0 : Int) + d808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10375 (p : Pattern) (guard : d4672 p = 1) : d1186 p ≤ (0 : Int) + d808 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10374 p hg
    simpa only [d4672, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d4672, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10376 (p : Pattern) (guard : d0 p = 1) : d1182 p ≤ (0 : Int) + d808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10377 (p : Pattern) (guard : d4673 p = 1) : d1187 p ≤ (0 : Int) + d808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10375 p hg
    simpa only [d4673, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d4673, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10378 (p : Pattern) (guard : d4672 p = 1) : d1188 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d4672, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d4672, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10379 (p : Pattern) (guard : d4673 p = 1) : d1189 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10378 p hg
    simpa only [d4673, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4673, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10380 (p : Pattern) (guard : d4673 p = 1) : d1190 p ≤ (0 : Int) + d4822 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1190, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10377 p hg
    simpa only [d1190, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1190, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10379 p hg
    simpa only [d1190, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10381 (p : Pattern) (guard : d4673 p = 1) : d1191 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1191, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10373 p hg
    simpa only [d1191, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1191, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10380 p hg
    simpa only [d1191, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10382 (p : Pattern) (guard : d4673 p = 1) : d1192 p ≤ (0 : Int) + d4824 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1192, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10366 p hg
    simpa only [d1192, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1192, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1192, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10383 (p : Pattern) (guard : d0 p = 1) : d1152 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10384 (p : Pattern) (guard : d4672 p = 1) : d1194 p ≤ (0 : Int) + d54 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10383 p hg
    simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9910 p hg
    simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10385 (p : Pattern) (guard : d4673 p = 1) : d1195 p ≤ (0 : Int) + d54 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10384 p hg
    simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10386 (p : Pattern) (guard : d4673 p = 1) : d1196 p ≤ (0 : Int) + d4821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1196, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10385 p hg
    simpa only [d1196, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1196, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d1196, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10387 (p : Pattern) (guard : d0 p = 1) : d1197 p ≤ (0 : Int) + d808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10388 (p : Pattern) (guard : d4672 p = 1) : d1198 p ≤ (0 : Int) + d808 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10387 p hg
    simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10389 (p : Pattern) (guard : d4673 p = 1) : d1199 p ≤ (0 : Int) + d808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10388 p hg
    simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10390 (p : Pattern) (guard : d4673 p = 1) : d1200 p ≤ (0 : Int) + d4822 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1200, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10389 p hg
    simpa only [d1200, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1200, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10379 p hg
    simpa only [d1200, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10391 (p : Pattern) (guard : d4673 p = 1) : d1201 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1201, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10386 p hg
    simpa only [d1201, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1201, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10390 p hg
    simpa only [d1201, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10392 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10393 (p : Pattern) (guard : d4672 p = 1) : d1202 p ≤ (0 : Int) + d63 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10392 p hg
    simpa only [d4672, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d4672, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10394 (p : Pattern) (guard : d0 p = 1) : d91 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10395 (p : Pattern) (guard : d4673 p = 1) : d1203 p ≤ (0 : Int) + d63 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10393 p hg
    simpa only [d4673, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10394 p hg
    simpa only [d4673, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10396 (p : Pattern) (guard : d4672 p = 1) : d91 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10397 (p : Pattern) (guard : d4673 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10396 p hg
    simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10398 (p : Pattern) (guard : d4673 p = 1) : d1204 p ≤ (0 : Int) + d4625 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1204, d4625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10395 p hg
    simpa only [d1204, d4625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1204, d4625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10397 p hg
    simpa only [d1204, d4625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10399 (p : Pattern) (guard : d4673 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare10400 (p : Pattern) (guard : d4673 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10397 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10401 (p : Pattern) (guard : d4673 p = 1) : d1205 p ≤ (0 : Int) + d4626 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1205, d4626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10398 p hg
    simpa only [d1205, d4626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1205, d4626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10400 p hg
    simpa only [d1205, d4626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10402 (p : Pattern) (guard : d4673 p = 1) : d1206 p ≤ (0 : Int) + d4825 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1206, d4825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10391 p hg
    simpa only [d1206, d4825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1206, d4825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10401 p hg
    simpa only [d1206, d4825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10403 (p : Pattern) (guard : d4673 p = 1) : d1207 p ≤ (0 : Int) + d4826 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1207, d4826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10382 p hg
    simpa only [d1207, d4826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1207, d4826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10402 p hg
    simpa only [d1207, d4826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10404 (p : Pattern) (guard : d0 p = 1) : d1208 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10405 (p : Pattern) (guard : d4148 p = 1) : d1185 p ≤ (0 : Int) + d950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1185, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1185, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1185, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9894 p hg
    simpa only [d4148, d1185, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10406 (p : Pattern) (guard : d4672 p = 1) : d1209 p ≤ (0 : Int) + d950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10404 p hg
    simpa only [d4672, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10405 p hg
    simpa only [d4672, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10407 (p : Pattern) (guard : d0 p = 1) : d1210 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10408 (p : Pattern) (guard : d4673 p = 1) : d1211 p ≤ (0 : Int) + d950 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10406 p hg
    simpa only [d4673, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10407 p hg
    simpa only [d4673, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10409 (p : Pattern) (guard : d0 p = 1) : d1212 p ≤ (0 : Int) + d47 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10410 (p : Pattern) (guard : d4672 p = 1) : d1213 p ≤ (0 : Int) + d47 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10409 p hg
    simpa only [d4672, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10350 p hg
    simpa only [d4672, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10411 (p : Pattern) (guard : d4673 p = 1) : d1214 p ≤ (0 : Int) + d47 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10410 p hg
    simpa only [d4673, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10352 p hg
    simpa only [d4673, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10412 (p : Pattern) (guard : d4673 p = 1) : d1215 p ≤ (0 : Int) + d4818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1215, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10408 p hg
    simpa only [d1215, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1215, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10411 p hg
    simpa only [d1215, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10413 (p : Pattern) (guard : d0 p = 1) : d1154 p ≤ (0 : Int) + d796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10414 (p : Pattern) (guard : d4672 p = 1) : d1216 p ≤ (0 : Int) + d796 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10413 p hg
    simpa only [d4672, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d4672, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10415 (p : Pattern) (guard : d0 p = 1) : d1182 p ≤ (0 : Int) + d796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10416 (p : Pattern) (guard : d4673 p = 1) : d1217 p ≤ (0 : Int) + d796 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10414 p hg
    simpa only [d4673, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10415 p hg
    simpa only [d4673, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10417 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10418 (p : Pattern) (guard : d4672 p = 1) : d1218 p ≤ (0 : Int) + d176 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10417 p hg
    simpa only [d4672, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d4672, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10419 (p : Pattern) (guard : d4673 p = 1) : d1219 p ≤ (0 : Int) + d176 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10418 p hg
    simpa only [d4673, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10363 p hg
    simpa only [d4673, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10420 (p : Pattern) (guard : d4673 p = 1) : d1220 p ≤ (0 : Int) + d4819 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1220, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10416 p hg
    simpa only [d1220, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1220, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10419 p hg
    simpa only [d1220, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10421 (p : Pattern) (guard : d4673 p = 1) : d1221 p ≤ (0 : Int) + d4820 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1221, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10412 p hg
    simpa only [d1221, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1221, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10420 p hg
    simpa only [d1221, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10422 (p : Pattern) (guard : d0 p = 1) : d1193 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10423 (p : Pattern) (guard : d4672 p = 1) : d1222 p ≤ (0 : Int) + d54 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10422 p hg
    simpa only [d4672, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d4672, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10424 (p : Pattern) (guard : d4673 p = 1) : d1223 p ≤ (0 : Int) + d54 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10423 p hg
    simpa only [d4673, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d4673, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10425 (p : Pattern) (guard : d4673 p = 1) : d1224 p ≤ (0 : Int) + d4821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1224, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10424 p hg
    simpa only [d1224, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1224, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d1224, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10426 (p : Pattern) (guard : d0 p = 1) : d1177 p ≤ (0 : Int) + d808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10427 (p : Pattern) (guard : d4672 p = 1) : d1225 p ≤ (0 : Int) + d808 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10426 p hg
    simpa only [d4672, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d4672, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10428 (p : Pattern) (guard : d4673 p = 1) : d1226 p ≤ (0 : Int) + d808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10427 p hg
    simpa only [d4673, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d4673, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10429 (p : Pattern) (guard : d4673 p = 1) : d1227 p ≤ (0 : Int) + d4822 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1227, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10428 p hg
    simpa only [d1227, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1227, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10379 p hg
    simpa only [d1227, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10430 (p : Pattern) (guard : d4673 p = 1) : d1228 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1228, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10425 p hg
    simpa only [d1228, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1228, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10429 p hg
    simpa only [d1228, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10431 (p : Pattern) (guard : d4673 p = 1) : d1229 p ≤ (0 : Int) + d4824 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1229, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10421 p hg
    simpa only [d1229, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1229, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10430 p hg
    simpa only [d1229, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10432 (p : Pattern) (guard : d0 p = 1) : d1185 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10433 (p : Pattern) (guard : d4672 p = 1) : d1230 p ≤ (0 : Int) + d54 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10432 p hg
    simpa only [d4672, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d4672, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10434 (p : Pattern) (guard : d4673 p = 1) : d1231 p ≤ (0 : Int) + d54 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10433 p hg
    simpa only [d4673, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d4673, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10435 (p : Pattern) (guard : d4673 p = 1) : d1232 p ≤ (0 : Int) + d4821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1232, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10434 p hg
    simpa only [d1232, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1232, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d1232, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10436 (p : Pattern) (guard : d4673 p = 1) : d1233 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1233, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10435 p hg
    simpa only [d1233, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1233, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10429 p hg
    simpa only [d1233, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10437 (p : Pattern) (guard : d4673 p = 1) : d1234 p ≤ (0 : Int) + d4827 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1234, d4827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10436 p hg
    simpa only [d1234, d4827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1234, d4827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d1234, d4827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10438 (p : Pattern) (guard : d4673 p = 1) : d1235 p ≤ (0 : Int) + d4828 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1235, d4828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10431 p hg
    simpa only [d1235, d4828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1235, d4828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10437 p hg
    simpa only [d1235, d4828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10439 (p : Pattern) (guard : d4673 p = 1) : d1236 p ≤ (0 : Int) + d4829 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1236, d4829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10403 p hg
    simpa only [d1236, d4829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1236, d4829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10438 p hg
    simpa only [d1236, d4829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10440 (p : Pattern) (guard : d0 p = 1) : d1237 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10441 (p : Pattern) (guard : d4672 p = 1) : d1238 p ≤ (0 : Int) + d950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10440 p hg
    simpa only [d4672, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d4672, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10442 (p : Pattern) (guard : d0 p = 1) : d1239 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10443 (p : Pattern) (guard : d4673 p = 1) : d1240 p ≤ (0 : Int) + d950 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10441 p hg
    simpa only [d4673, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10442 p hg
    simpa only [d4673, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10444 (p : Pattern) (guard : d0 p = 1) : d1241 p ≤ (0 : Int) + d47 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10445 (p : Pattern) (guard : d4672 p = 1) : d1242 p ≤ (0 : Int) + d47 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10444 p hg
    simpa only [d4672, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10350 p hg
    simpa only [d4672, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10446 (p : Pattern) (guard : d4673 p = 1) : d1243 p ≤ (0 : Int) + d47 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10445 p hg
    simpa only [d4673, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10352 p hg
    simpa only [d4673, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10447 (p : Pattern) (guard : d4673 p = 1) : d1244 p ≤ (0 : Int) + d4818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1244, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10443 p hg
    simpa only [d1244, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1244, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10446 p hg
    simpa only [d1244, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10448 (p : Pattern) (guard : d0 p = 1) : d1208 p ≤ (0 : Int) + d796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10449 (p : Pattern) (guard : d4672 p = 1) : d1245 p ≤ (0 : Int) + d796 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10448 p hg
    simpa only [d4672, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d4672, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10450 (p : Pattern) (guard : d0 p = 1) : d1246 p ≤ (0 : Int) + d796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10451 (p : Pattern) (guard : d4673 p = 1) : d1247 p ≤ (0 : Int) + d796 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10449 p hg
    simpa only [d4673, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10450 p hg
    simpa only [d4673, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10452 (p : Pattern) (guard : d4673 p = 1) : d1248 p ≤ (0 : Int) + d4819 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1248, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10451 p hg
    simpa only [d1248, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1248, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10419 p hg
    simpa only [d1248, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10453 (p : Pattern) (guard : d4673 p = 1) : d1249 p ≤ (0 : Int) + d4820 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1249, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10447 p hg
    simpa only [d1249, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1249, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10452 p hg
    simpa only [d1249, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10454 (p : Pattern) (guard : d0 p = 1) : d1197 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10455 (p : Pattern) (guard : d4672 p = 1) : d1250 p ≤ (0 : Int) + d54 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10454 p hg
    simpa only [d4672, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d4672, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10456 (p : Pattern) (guard : d4673 p = 1) : d1251 p ≤ (0 : Int) + d54 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10455 p hg
    simpa only [d4673, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d4673, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10457 (p : Pattern) (guard : d4673 p = 1) : d1252 p ≤ (0 : Int) + d4821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1252, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10456 p hg
    simpa only [d1252, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1252, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d1252, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10458 (p : Pattern) (guard : d0 p = 1) : d1193 p ≤ (0 : Int) + d808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10459 (p : Pattern) (guard : d4672 p = 1) : d1253 p ≤ (0 : Int) + d808 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10458 p hg
    simpa only [d4672, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d4672, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10460 (p : Pattern) (guard : d4673 p = 1) : d1254 p ≤ (0 : Int) + d808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10459 p hg
    simpa only [d4673, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d4673, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10461 (p : Pattern) (guard : d4673 p = 1) : d1255 p ≤ (0 : Int) + d4822 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1255, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10460 p hg
    simpa only [d1255, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1255, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10379 p hg
    simpa only [d1255, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10462 (p : Pattern) (guard : d4673 p = 1) : d1256 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1256, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10457 p hg
    simpa only [d1256, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1256, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10461 p hg
    simpa only [d1256, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10463 (p : Pattern) (guard : d4673 p = 1) : d1257 p ≤ (0 : Int) + d4824 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1257, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10453 p hg
    simpa only [d1257, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1257, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10462 p hg
    simpa only [d1257, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10464 (p : Pattern) (guard : d4673 p = 1) : d1258 p ≤ (0 : Int) + d4825 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1258, d4825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1258, d4825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1258, d4825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10401 p hg
    simpa only [d1258, d4825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10465 (p : Pattern) (guard : d4673 p = 1) : d1259 p ≤ (0 : Int) + d4826 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1259, d4826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10463 p hg
    simpa only [d1259, d4826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1259, d4826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10464 p hg
    simpa only [d1259, d4826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10466 (p : Pattern) (guard : d0 p = 1) : d1152 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10467 (p : Pattern) (guard : d4672 p = 1) : d1194 p ≤ (0 : Int) + d950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10466 p hg
    simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9859 p hg
    simpa only [d4672, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10468 (p : Pattern) (guard : d0 p = 1) : d1179 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10469 (p : Pattern) (guard : d4673 p = 1) : d1195 p ≤ (0 : Int) + d950 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10467 p hg
    simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10468 p hg
    simpa only [d4673, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10470 (p : Pattern) (guard : d4673 p = 1) : d1260 p ≤ (0 : Int) + d4818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1260, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10469 p hg
    simpa only [d1260, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1260, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10411 p hg
    simpa only [d1260, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10471 (p : Pattern) (guard : d0 p = 1) : d1197 p ≤ (0 : Int) + d796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10472 (p : Pattern) (guard : d4672 p = 1) : d1198 p ≤ (0 : Int) + d796 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10471 p hg
    simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d4672, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10473 (p : Pattern) (guard : d4673 p = 1) : d1199 p ≤ (0 : Int) + d796 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10472 p hg
    simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10415 p hg
    simpa only [d4673, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10474 (p : Pattern) (guard : d4673 p = 1) : d1261 p ≤ (0 : Int) + d4819 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1261, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10473 p hg
    simpa only [d1261, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1261, d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10419 p hg
    simpa only [d1261, d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10475 (p : Pattern) (guard : d4673 p = 1) : d1262 p ≤ (0 : Int) + d4820 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1262, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10470 p hg
    simpa only [d1262, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1262, d4820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10474 p hg
    simpa only [d1262, d4820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10476 (p : Pattern) (guard : d0 p = 1) : d1177 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10477 (p : Pattern) (guard : d4672 p = 1) : d1177 p ≤ (0 : Int) + d54 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10476 p hg
    simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10478 (p : Pattern) (guard : d4673 p = 1) : d1263 p ≤ (0 : Int) + d54 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10477 p hg
    simpa only [d4673, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d4673, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10479 (p : Pattern) (guard : d4673 p = 1) : d1264 p ≤ (0 : Int) + d4821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1264, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10478 p hg
    simpa only [d1264, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1264, d4821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d1264, d4821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10480 (p : Pattern) (guard : d4673 p = 1) : d1265 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1265, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10479 p hg
    simpa only [d1265, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1265, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10429 p hg
    simpa only [d1265, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10481 (p : Pattern) (guard : d4673 p = 1) : d1266 p ≤ (0 : Int) + d4824 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1266, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10475 p hg
    simpa only [d1266, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1266, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10480 p hg
    simpa only [d1266, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10482 (p : Pattern) (guard : d4673 p = 1) : d1267 p ≤ (0 : Int) + d4827 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1267, d4827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10430 p hg
    simpa only [d1267, d4827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1267, d4827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d1267, d4827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10483 (p : Pattern) (guard : d4673 p = 1) : d1268 p ≤ (0 : Int) + d4828 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1268, d4828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10481 p hg
    simpa only [d1268, d4828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1268, d4828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10482 p hg
    simpa only [d1268, d4828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10484 (p : Pattern) (guard : d4673 p = 1) : d1269 p ≤ (0 : Int) + d4829 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1269, d4829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10465 p hg
    simpa only [d1269, d4829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1269, d4829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10483 p hg
    simpa only [d1269, d4829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10485 (p : Pattern) (guard : d4673 p = 1) : d1270 p ≤ (0 : Int) + d4829 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10439 p hg
    simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10484 p hg
    simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10486 (p : Pattern) (guard : d0 p = 1) : d1271 p ≤ (0 : Int) + d1043 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10487 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10488 (p : Pattern) (guard : d4148 p = 1) : d1272 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1272, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1272, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1272, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10487 p hg
    simpa only [d4148, d1272, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10489 (p : Pattern) (guard : d4672 p = 1) : d1273 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10486 p hg
    simpa only [d4672, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10488 p hg
    simpa only [d4672, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10490 (p : Pattern) (guard : d0 p = 1) : d1275 p ≤ (0 : Int) + d1043 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10491 (p : Pattern) (guard : d4673 p = 1) : d1276 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10489 p hg
    simpa only [d4673, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10490 p hg
    simpa only [d4673, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10492 (p : Pattern) (guard : d0 p = 1) : d1277 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10493 (p : Pattern) (guard : d4672 p = 1) : d1279 p ≤ (0 : Int) + d126 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10492 p hg
    simpa only [d4672, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d4672, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10494 (p : Pattern) (guard : d0 p = 1) : d1280 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10495 (p : Pattern) (guard : d4673 p = 1) : d1281 p ≤ (0 : Int) + d126 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10493 p hg
    simpa only [d4673, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10494 p hg
    simpa only [d4673, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10496 (p : Pattern) (guard : d4673 p = 1) : d1282 p ≤ (0 : Int) + d4830 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1282, d4830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10491 p hg
    simpa only [d1282, d4830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1282, d4830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10495 p hg
    simpa only [d1282, d4830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10497 (p : Pattern) (guard : d0 p = 1) : d1283 p ≤ (0 : Int) + d862 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10498 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10499 (p : Pattern) (guard : d4148 p = 1) : d1284 p ≤ (0 : Int) + d862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1284, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1284, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1284, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10498 p hg
    simpa only [d4148, d1284, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
