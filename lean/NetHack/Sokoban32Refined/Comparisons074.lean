/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10360 (p : Pattern) (guard : d1963 p = 1) : d559 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10358 p hg
    simpa only [d1963, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10359 p hg
    simpa only [d1963, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10361 (p : Pattern) (guard : d1962 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10362 (p : Pattern) (guard : d1966 p = 1) : d547 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10316 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10342 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10363 (p : Pattern) (guard : d1967 p = 1) : d557 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10361 p hg
    simpa only [d1967, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10362 p hg
    simpa only [d1967, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10364 (p : Pattern) (guard : d1968 p = 1) : d560 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10360 p hg
    simpa only [d1968, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10363 p hg
    simpa only [d1968, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10365 (p : Pattern) (guard : d1969 p = 1) : d561 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10355 p hg
    simpa only [d1969, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10364 p hg
    simpa only [d1969, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10366 (p : Pattern) (guard : d1957 p = 1) : d562 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10309 p hg
    simpa only [d1957, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10367 (p : Pattern) (guard : d1958 p = 1) : d563 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10357 p hg
    simpa only [d1958, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10366 p hg
    simpa only [d1958, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10368 (p : Pattern) (guard : d1961 p = 1) : d562 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10336 p hg
    simpa only [d1961, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10369 (p : Pattern) (guard : d1962 p = 1) : d563 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1962, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10368 p hg
    simpa only [d1962, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10370 (p : Pattern) (guard : d1963 p = 1) : d563 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10367 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10371 (p : Pattern) (guard : d0 p = 1) : d564 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10372 (p : Pattern) (guard : d1966 p = 1) : d565 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10316 p hg
    simpa only [d1966, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10371 p hg
    simpa only [d1966, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10373 (p : Pattern) (guard : d1967 p = 1) : d566 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d1967, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d1967, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10374 (p : Pattern) (guard : d1968 p = 1) : d567 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10370 p hg
    simpa only [d1968, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10373 p hg
    simpa only [d1968, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10375 (p : Pattern) (guard : d1956 p = 1) : d540 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9606 p hg
    simpa only [d1956, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1956, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10376 (p : Pattern) (guard : d1957 p = 1) : d541 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10307 p hg
    simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10375 p hg
    simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10377 (p : Pattern) (guard : d1962 p = 1) : d563 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d1962, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10368 p hg
    simpa only [d1962, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10378 (p : Pattern) (guard : d0 p = 1) : d568 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10379 (p : Pattern) (guard : d1966 p = 1) : d569 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10331 p hg
    simpa only [d1966, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10378 p hg
    simpa only [d1966, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10380 (p : Pattern) (guard : d1967 p = 1) : d570 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10377 p hg
    simpa only [d1967, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10379 p hg
    simpa only [d1967, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10381 (p : Pattern) (guard : d0 p = 1) : d562 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10382 (p : Pattern) (guard : d1966 p = 1) : d563 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1966, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1966, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10383 (p : Pattern) (guard : d0 p = 1) : d565 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10384 (p : Pattern) (guard : d1971 p = 1) : d566 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10382 p hg
    simpa only [d1971, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10383 p hg
    simpa only [d1971, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10385 (p : Pattern) (guard : d1972 p = 1) : d571 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10380 p hg
    simpa only [d1972, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10384 p hg
    simpa only [d1972, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10386 (p : Pattern) (guard : d1973 p = 1) : d572 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10374 p hg
    simpa only [d1973, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10385 p hg
    simpa only [d1973, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10387 (p : Pattern) (guard : d1974 p = 1) : d573 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10365 p hg
    simpa only [d1974, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10386 p hg
    simpa only [d1974, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10388 (p : Pattern) (guard : d1975 p = 1) : d574 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d574, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10347 p hg
    simpa only [d1975, d574, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d574, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10387 p hg
    simpa only [d1975, d574, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10389 (p : Pattern) (guard : d1963 p = 1) : d575 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d575, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10328 p hg
    simpa only [d1963, d575, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d575, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10317 p hg
    simpa only [d1963, d575, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10390 (p : Pattern) (guard : d1957 p = 1) : d540 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10356 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10375 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10391 (p : Pattern) (guard : d1961 p = 1) : d576 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10310 p hg
    simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10392 (p : Pattern) (guard : d1962 p = 1) : d577 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10390 p hg
    simpa only [d1962, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10391 p hg
    simpa only [d1962, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10393 (p : Pattern) (guard : d1961 p = 1) : d546 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10292 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10315 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10394 (p : Pattern) (guard : d0 p = 1) : d578 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10395 (p : Pattern) (guard : d1966 p = 1) : d579 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10393 p hg
    simpa only [d1966, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10394 p hg
    simpa only [d1966, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10396 (p : Pattern) (guard : d1967 p = 1) : d580 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10392 p hg
    simpa only [d1967, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10395 p hg
    simpa only [d1967, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10397 (p : Pattern) (guard : d1968 p = 1) : d581 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d581, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10389 p hg
    simpa only [d1968, d581, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d581, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10396 p hg
    simpa only [d1968, d581, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10398 (p : Pattern) (guard : d1969 p = 1) : d582 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10324 p hg
    simpa only [d1969, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10397 p hg
    simpa only [d1969, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10399 (p : Pattern) (guard : d1957 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10309 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10336 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10400 (p : Pattern) (guard : d1962 p = 1) : d543 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d1962, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1962, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10401 (p : Pattern) (guard : d1963 p = 1) : d544 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10328 p hg
    simpa only [d1963, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10400 p hg
    simpa only [d1963, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10402 (p : Pattern) (guard : d1968 p = 1) : d550 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10401 p hg
    simpa only [d1968, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10344 p hg
    simpa only [d1968, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10403 (p : Pattern) (guard : d1956 p = 1) : d539 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9633 p hg
    simpa only [d1956, d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6387 p hg
    simpa only [d1956, d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10404 (p : Pattern) (guard : d1957 p = 1) : d583 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10326 p hg
    simpa only [d1957, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10403 p hg
    simpa only [d1957, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10405 (p : Pattern) (guard : d1962 p = 1) : d584 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d584, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10404 p hg
    simpa only [d1962, d584, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d584, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1962, d584, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10406 (p : Pattern) (guard : d1967 p = 1) : d585 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d585, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10405 p hg
    simpa only [d1967, d585, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d585, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10343 p hg
    simpa only [d1967, d585, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10407 (p : Pattern) (guard : d1961 p = 1) : d576 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10375 p hg
    simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10408 (p : Pattern) (guard : d0 p = 1) : d576 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10409 (p : Pattern) (guard : d1966 p = 1) : d576 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10407 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10408 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10410 (p : Pattern) (guard : d1971 p = 1) : d586 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d586, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10409 p hg
    simpa only [d1971, d586, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d586, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10394 p hg
    simpa only [d1971, d586, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10411 (p : Pattern) (guard : d1972 p = 1) : d587 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d587, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10406 p hg
    simpa only [d1972, d587, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d587, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10410 p hg
    simpa only [d1972, d587, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10412 (p : Pattern) (guard : d1973 p = 1) : d588 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10402 p hg
    simpa only [d1973, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10411 p hg
    simpa only [d1973, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10413 (p : Pattern) (guard : d1974 p = 1) : d589 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10398 p hg
    simpa only [d1974, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10412 p hg
    simpa only [d1974, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10414 (p : Pattern) (guard : d1963 p = 1) : d541 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10358 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10361 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10415 (p : Pattern) (guard : d1968 p = 1) : d558 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10414 p hg
    simpa only [d1968, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10363 p hg
    simpa only [d1968, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10416 (p : Pattern) (guard : d1962 p = 1) : d541 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10417 (p : Pattern) (guard : d1967 p = 1) : d557 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10416 p hg
    simpa only [d1967, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10362 p hg
    simpa only [d1967, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10418 (p : Pattern) (guard : d1966 p = 1) : d576 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10391 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10408 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10419 (p : Pattern) (guard : d1971 p = 1) : d586 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10418 p hg
    simpa only [d1971, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10394 p hg
    simpa only [d1971, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10420 (p : Pattern) (guard : d1972 p = 1) : d590 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10417 p hg
    simpa only [d1972, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10419 p hg
    simpa only [d1972, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10421 (p : Pattern) (guard : d1973 p = 1) : d591 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10415 p hg
    simpa only [d1973, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10420 p hg
    simpa only [d1973, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10422 (p : Pattern) (guard : d1967 p = 1) : d563 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10377 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10382 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10423 (p : Pattern) (guard : d1972 p = 1) : d567 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10422 p hg
    simpa only [d1972, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10384 p hg
    simpa only [d1972, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10424 (p : Pattern) (guard : d0 p = 1) : d540 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10425 (p : Pattern) (guard : d1961 p = 1) : d541 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10334 p hg
    simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10424 p hg
    simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10426 (p : Pattern) (guard : d1966 p = 1) : d563 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10425 p hg
    simpa only [d1966, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1966, d563, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10427 (p : Pattern) (guard : d1971 p = 1) : d566 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d566, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10426 p hg
    simpa only [d1971, d566, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d566, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10383 p hg
    simpa only [d1971, d566, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10428 (p : Pattern) (guard : d1976 p = 1) : d592 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d592, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10427 p hg
    simpa only [d1976, d592, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d592, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1976, d592, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10429 (p : Pattern) (guard : d1977 p = 1) : d593 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10423 p hg
    simpa only [d1977, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10428 p hg
    simpa only [d1977, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10430 (p : Pattern) (guard : d1978 p = 1) : d594 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10421 p hg
    simpa only [d1978, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10429 p hg
    simpa only [d1978, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10431 (p : Pattern) (guard : d1979 p = 1) : d595 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10413 p hg
    simpa only [d1979, d595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10430 p hg
    simpa only [d1979, d595, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10432 (p : Pattern) (guard : d1980 p = 1) : d596 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10388 p hg
    simpa only [d1980, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10431 p hg
    simpa only [d1980, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10433 (p : Pattern) (guard : d1958 p = 1) : d597 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d597, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10327 p hg
    simpa only [d1958, d597, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d597, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10366 p hg
    simpa only [d1958, d597, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10434 (p : Pattern) (guard : d1962 p = 1) : d598 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d1962, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10368 p hg
    simpa only [d1962, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10435 (p : Pattern) (guard : d1963 p = 1) : d599 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d599, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10433 p hg
    simpa only [d1963, d599, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d599, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10434 p hg
    simpa only [d1963, d599, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10436 (p : Pattern) (guard : d1962 p = 1) : d598 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10335 p hg
    simpa only [d1962, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10368 p hg
    simpa only [d1962, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10437 (p : Pattern) (guard : d1966 p = 1) : d600 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10341 p hg
    simpa only [d1966, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10371 p hg
    simpa only [d1966, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10438 (p : Pattern) (guard : d1967 p = 1) : d601 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10436 p hg
    simpa only [d1967, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10437 p hg
    simpa only [d1967, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10439 (p : Pattern) (guard : d1968 p = 1) : d602 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d602, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10435 p hg
    simpa only [d1968, d602, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d602, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10438 p hg
    simpa only [d1968, d602, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10440 (p : Pattern) (guard : d1962 p = 1) : d603 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d603, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10404 p hg
    simpa only [d1962, d603, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d603, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10368 p hg
    simpa only [d1962, d603, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10441 (p : Pattern) (guard : d0 p = 1) : d551 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10442 (p : Pattern) (guard : d1961 p = 1) : d551 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10329 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10441 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10443 (p : Pattern) (guard : d1966 p = 1) : d604 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10442 p hg
    simpa only [d1966, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10378 p hg
    simpa only [d1966, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10444 (p : Pattern) (guard : d1967 p = 1) : d605 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d605, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10440 p hg
    simpa only [d1967, d605, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d605, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10443 p hg
    simpa only [d1967, d605, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10445 (p : Pattern) (guard : d0 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10446 (p : Pattern) (guard : d1961 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10334 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10445 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10447 (p : Pattern) (guard : d1966 p = 1) : d598 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10446 p hg
    simpa only [d1966, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1966, d598, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10448 (p : Pattern) (guard : d0 p = 1) : d600 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10449 (p : Pattern) (guard : d1971 p = 1) : d601 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10447 p hg
    simpa only [d1971, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10448 p hg
    simpa only [d1971, d601, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10450 (p : Pattern) (guard : d1972 p = 1) : d606 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d606, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10444 p hg
    simpa only [d1972, d606, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d606, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10449 p hg
    simpa only [d1972, d606, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10451 (p : Pattern) (guard : d1973 p = 1) : d607 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10439 p hg
    simpa only [d1973, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10450 p hg
    simpa only [d1973, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10452 (p : Pattern) (guard : d1974 p = 1) : d608 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10346 p hg
    simpa only [d1974, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10451 p hg
    simpa only [d1974, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10453 (p : Pattern) (guard : d1953 p = 1) : d540 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10348 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10356 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10454 (p : Pattern) (guard : d1957 p = 1) : d576 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10281 p hg
    simpa only [d1957, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10455 (p : Pattern) (guard : d1958 p = 1) : d577 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10453 p hg
    simpa only [d1958, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10454 p hg
    simpa only [d1958, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10456 (p : Pattern) (guard : d1957 p = 1) : d540 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10281 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10310 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10457 (p : Pattern) (guard : d1962 p = 1) : d577 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10456 p hg
    simpa only [d1962, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10391 p hg
    simpa only [d1962, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10458 (p : Pattern) (guard : d1963 p = 1) : d577 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10455 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10457 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10459 (p : Pattern) (guard : d1967 p = 1) : d580 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10457 p hg
    simpa only [d1967, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10395 p hg
    simpa only [d1967, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10460 (p : Pattern) (guard : d1968 p = 1) : d609 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10458 p hg
    simpa only [d1968, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10459 p hg
    simpa only [d1968, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10461 (p : Pattern) (guard : d1961 p = 1) : d540 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10310 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10337 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10462 (p : Pattern) (guard : d1966 p = 1) : d577 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10461 p hg
    simpa only [d1966, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10408 p hg
    simpa only [d1966, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10463 (p : Pattern) (guard : d0 p = 1) : d579 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10464 (p : Pattern) (guard : d1971 p = 1) : d580 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10462 p hg
    simpa only [d1971, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10463 p hg
    simpa only [d1971, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10465 (p : Pattern) (guard : d1972 p = 1) : d580 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10396 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10464 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10466 (p : Pattern) (guard : d1973 p = 1) : d610 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10460 p hg
    simpa only [d1973, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10465 p hg
    simpa only [d1973, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10467 (p : Pattern) (guard : d1967 p = 1) : d577 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10392 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10462 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10468 (p : Pattern) (guard : d1972 p = 1) : d609 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10467 p hg
    simpa only [d1972, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10464 p hg
    simpa only [d1972, d609, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10469 (p : Pattern) (guard : d1961 p = 1) : d540 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10375 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10424 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10470 (p : Pattern) (guard : d1966 p = 1) : d577 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10469 p hg
    simpa only [d1966, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10408 p hg
    simpa only [d1966, d577, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10471 (p : Pattern) (guard : d1971 p = 1) : d580 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10470 p hg
    simpa only [d1971, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10463 p hg
    simpa only [d1971, d580, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10472 (p : Pattern) (guard : d1976 p = 1) : d580 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10471 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10473 (p : Pattern) (guard : d1977 p = 1) : d610 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10468 p hg
    simpa only [d1977, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10472 p hg
    simpa only [d1977, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10474 (p : Pattern) (guard : d1978 p = 1) : d610 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10466 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10473 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10475 (p : Pattern) (guard : d1979 p = 1) : d611 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d611, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10452 p hg
    simpa only [d1979, d611, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d611, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10474 p hg
    simpa only [d1979, d611, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10476 (p : Pattern) (guard : d0 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10477 (p : Pattern) (guard : d1961 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10336 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10476 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10478 (p : Pattern) (guard : d1966 p = 1) : d598 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10477 p hg
    simpa only [d1966, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1966, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10479 (p : Pattern) (guard : d1967 p = 1) : d612 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d612, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10440 p hg
    simpa only [d1967, d612, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d612, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10478 p hg
    simpa only [d1967, d612, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10480 (p : Pattern) (guard : d1972 p = 1) : d613 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d613, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10479 p hg
    simpa only [d1972, d613, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d613, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10449 p hg
    simpa only [d1972, d613, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10481 (p : Pattern) (guard : d0 p = 1) : d539 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10482 (p : Pattern) (guard : d1961 p = 1) : d539 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10403 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10481 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10483 (p : Pattern) (guard : d1966 p = 1) : d598 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d598, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10482 p hg
    simpa only [d1966, d598, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d598, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1966, d598, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10484 (p : Pattern) (guard : d1971 p = 1) : d601 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d601, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10483 p hg
    simpa only [d1971, d601, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d601, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10448 p hg
    simpa only [d1971, d601, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10485 (p : Pattern) (guard : d0 p = 1) : d586 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10486 (p : Pattern) (guard : d1976 p = 1) : d614 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d614, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10484 p hg
    simpa only [d1976, d614, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d614, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10485 p hg
    simpa only [d1976, d614, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10487 (p : Pattern) (guard : d1977 p = 1) : d615 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10480 p hg
    simpa only [d1977, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10486 p hg
    simpa only [d1977, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10488 (p : Pattern) (guard : d1978 p = 1) : d616 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10412 p hg
    simpa only [d1978, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10487 p hg
    simpa only [d1978, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10489 (p : Pattern) (guard : d1976 p = 1) : d617 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10471 p hg
    simpa only [d1976, d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10490 (p : Pattern) (guard : d1977 p = 1) : d618 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10468 p hg
    simpa only [d1977, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10489 p hg
    simpa only [d1977, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10491 (p : Pattern) (guard : d1971 p = 1) : d576 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10409 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10408 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10492 (p : Pattern) (guard : d1976 p = 1) : d619 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d619, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10491 p hg
    simpa only [d1976, d619, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d619, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1976, d619, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10493 (p : Pattern) (guard : d0 p = 1) : d620 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10494 (p : Pattern) (guard : d1981 p = 1) : d621 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10492 p hg
    simpa only [d1981, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10493 p hg
    simpa only [d1981, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10495 (p : Pattern) (guard : d1982 p = 1) : d622 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10490 p hg
    simpa only [d1982, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10494 p hg
    simpa only [d1982, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10496 (p : Pattern) (guard : d1983 p = 1) : d623 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d623, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10488 p hg
    simpa only [d1983, d623, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d623, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10495 p hg
    simpa only [d1983, d623, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10497 (p : Pattern) (guard : d1984 p = 1) : d624 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10475 p hg
    simpa only [d1984, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10496 p hg
    simpa only [d1984, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10498 (p : Pattern) (guard : d1985 p = 1) : d625 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10432 p hg
    simpa only [d1985, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10497 p hg
    simpa only [d1985, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10499 (p : Pattern) (guard : d0 p = 1) : d552 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
