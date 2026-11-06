/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9380 (p : Pattern) (guard : d1946 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9376 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1945 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9379 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9381 (p : Pattern) (guard : d1949 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9382 (p : Pattern) (guard : d1950 p = 1) : d0 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9380 p hg
    simpa only [d1950, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9381 p hg
    simpa only [d1950, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9383 (p : Pattern) (guard : d1954 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9384 (p : Pattern) (guard : d1955 p = 1) : d0 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9382 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9383 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9385 (p : Pattern) (guard : d1944 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9386 (p : Pattern) (guard : d1945 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9375 p hg
    simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9385 p hg
    simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9387 (p : Pattern) (guard : d1947 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9388 (p : Pattern) (guard : d1948 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9378 p hg
    simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9387 p hg
    simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9389 (p : Pattern) (guard : d1949 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9386 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9388 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9390 (p : Pattern) (guard : d1953 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9391 (p : Pattern) (guard : d1954 p = 1) : d0 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9389 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9390 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9392 (p : Pattern) (guard : d1958 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9393 (p : Pattern) (guard : d1959 p = 1) : d0 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9391 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9392 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9394 (p : Pattern) (guard : d1960 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9384 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9393 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9395 (p : Pattern) (guard : d1944 p = 1) : d0 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9371 p hg
    simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9377 p hg
    simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9396 (p : Pattern) (guard : d985 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9397 (p : Pattern) (guard : d1943 p = 1) : d0 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9396 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9398 (p : Pattern) (guard : d1293 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9399 (p : Pattern) (guard : d1947 p = 1) : d0 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9397 p hg
    simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9398 p hg
    simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9400 (p : Pattern) (guard : d1948 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9395 p hg
    simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9399 p hg
    simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9401 (p : Pattern) (guard : d1949 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9379 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9400 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9402 (p : Pattern) (guard : d1954 p = 1) : d0 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9401 p hg
    simpa only [d1954, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9390 p hg
    simpa only [d1954, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9403 (p : Pattern) (guard : d1959 p = 1) : d0 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9402 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9392 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9404 (p : Pattern) (guard : d1951 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9405 (p : Pattern) (guard : d1952 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9399 p hg
    simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9404 p hg
    simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9406 (p : Pattern) (guard : d1953 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9388 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9405 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9407 (p : Pattern) (guard : d1957 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9408 (p : Pattern) (guard : d1958 p = 1) : d0 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9406 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9407 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9409 (p : Pattern) (guard : d1962 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9410 (p : Pattern) (guard : d1963 p = 1) : d0 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9408 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9409 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9411 (p : Pattern) (guard : d1964 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9403 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9410 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9412 (p : Pattern) (guard : d1965 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9394 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9411 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9413 (p : Pattern) (guard : d1943 p = 1) : d0 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9396 p hg
    simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9414 (p : Pattern) (guard : d1947 p = 1) : d0 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9413 p hg
    simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9398 p hg
    simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9415 (p : Pattern) (guard : d985 p = 1) : d0 p ≤ (0 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9416 (p : Pattern) (guard : d1293 p = 1) : d0 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9415 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9417 (p : Pattern) (guard : d1951 p = 1) : d0 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9416 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9418 (p : Pattern) (guard : d1952 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9414 p hg
    simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9417 p hg
    simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9419 (p : Pattern) (guard : d1953 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9400 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9418 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9420 (p : Pattern) (guard : d1958 p = 1) : d0 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9419 p hg
    simpa only [d1958, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9407 p hg
    simpa only [d1958, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9421 (p : Pattern) (guard : d1963 p = 1) : d0 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9420 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9409 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9422 (p : Pattern) (guard : d1956 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9417 p hg
    simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9423 (p : Pattern) (guard : d1957 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9405 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9422 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9424 (p : Pattern) (guard : d1961 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9425 (p : Pattern) (guard : d1962 p = 1) : d0 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9423 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9424 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9426 (p : Pattern) (guard : d1966 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9427 (p : Pattern) (guard : d1967 p = 1) : d0 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9425 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9426 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9428 (p : Pattern) (guard : d1968 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9421 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9427 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9429 (p : Pattern) (guard : d1969 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9411 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9428 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9430 (p : Pattern) (guard : d1970 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9412 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9429 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9431 (p : Pattern) (guard : d1963 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9432 (p : Pattern) (guard : d1964 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9393 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9431 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9433 (p : Pattern) (guard : d1967 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9434 (p : Pattern) (guard : d1968 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9410 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9433 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9435 (p : Pattern) (guard : d1969 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9432 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9434 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9436 (p : Pattern) (guard : d1971 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9437 (p : Pattern) (guard : d1972 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9427 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9436 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9438 (p : Pattern) (guard : d1973 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9434 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9437 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9439 (p : Pattern) (guard : d1974 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9435 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9438 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9440 (p : Pattern) (guard : d1975 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9430 p hg
    simpa only [d1975, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9439 p hg
    simpa only [d1975, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9441 (p : Pattern) (guard : d1293 p = 1) : d0 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9442 (p : Pattern) (guard : d1951 p = 1) : d0 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9441 p hg
    simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9443 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9444 (p : Pattern) (guard : d1956 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9442 p hg
    simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9443 p hg
    simpa only [d1956, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9445 (p : Pattern) (guard : d1957 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9418 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9444 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9446 (p : Pattern) (guard : d1962 p = 1) : d0 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9445 p hg
    simpa only [d1962, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9424 p hg
    simpa only [d1962, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9447 (p : Pattern) (guard : d1967 p = 1) : d0 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9446 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9426 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9448 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9449 (p : Pattern) (guard : d1961 p = 1) : d0 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9422 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9448 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9450 (p : Pattern) (guard : d1966 p = 1) : d0 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9449 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9451 (p : Pattern) (guard : d1971 p = 1) : d0 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9450 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9452 (p : Pattern) (guard : d1972 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9447 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9453 (p : Pattern) (guard : d1973 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9428 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9452 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9454 (p : Pattern) (guard : d1974 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9429 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9455 (p : Pattern) (guard : d1976 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9456 (p : Pattern) (guard : d1977 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9437 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9455 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9457 (p : Pattern) (guard : d1978 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9438 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9456 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9458 (p : Pattern) (guard : d1979 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9454 p hg
    simpa only [d1979, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9457 p hg
    simpa only [d1979, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9459 (p : Pattern) (guard : d1980 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9440 p hg
    simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9458 p hg
    simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9460 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9461 (p : Pattern) (guard : d1961 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9444 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9462 (p : Pattern) (guard : d1966 p = 1) : d0 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9461 p hg
    simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9463 (p : Pattern) (guard : d1971 p = 1) : d0 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9464 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9465 (p : Pattern) (guard : d1976 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9463 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9464 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9466 (p : Pattern) (guard : d1977 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9452 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9465 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9467 (p : Pattern) (guard : d1978 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9468 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9469 (p : Pattern) (guard : d1981 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9455 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9468 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9470 (p : Pattern) (guard : d1982 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9456 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9469 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9471 (p : Pattern) (guard : d1983 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9467 p hg
    simpa only [d1983, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9470 p hg
    simpa only [d1983, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9472 (p : Pattern) (guard : d1984 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9458 p hg
    simpa only [d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9471 p hg
    simpa only [d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9473 (p : Pattern) (guard : d1985 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9459 p hg
    simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9472 p hg
    simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9474 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9475 (p : Pattern) (guard : d1981 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9465 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9474 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9476 (p : Pattern) (guard : d1982 p = 1) : d0 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9475 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9477 (p : Pattern) (guard : d1986 p = 1) : d0 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9469 p hg
    simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9468 p hg
    simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9478 (p : Pattern) (guard : d1987 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9476 p hg
    simpa only [d1987, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9477 p hg
    simpa only [d1987, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9479 (p : Pattern) (guard : d1988 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9471 p hg
    simpa only [d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9478 p hg
    simpa only [d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9480 (p : Pattern) (guard : d1989 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9472 p hg
    simpa only [d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9479 p hg
    simpa only [d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9481 (p : Pattern) (guard : d1990 p = 1) : d0 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9473 p hg
    simpa only [d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9480 p hg
    simpa only [d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9482 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9483 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9484 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9483 p hg
    simpa only [d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9485 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9482 p hg
    simpa only [d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9484 p hg
    simpa only [d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9486 (p : Pattern) (guard : d1943 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare9487 (p : Pattern) (guard : d1944 p = 1) : d7 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9483 p hg
    simpa only [d1944, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9488 (p : Pattern) (guard : d1945 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9482 p hg
    simpa only [d1945, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9487 p hg
    simpa only [d1945, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9489 (p : Pattern) (guard : d1946 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9485 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1945 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9488 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9490 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9491 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9492 (p : Pattern) (guard : d1944 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d1944, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9493 (p : Pattern) (guard : d1945 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9491 p hg
    simpa only [d1945, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9492 p hg
    simpa only [d1945, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9494 (p : Pattern) (guard : d1943 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d1943, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9495 (p : Pattern) (guard : d1944 p = 1) : d12 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d1944, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1944, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9496 (p : Pattern) (guard : d1943 p = 1) : d10 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d1943, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d1943, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9497 (p : Pattern) (guard : d1947 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9496 p hg
    simpa only [d1947, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9498 (p : Pattern) (guard : d1948 p = 1) : d14 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9495 p hg
    simpa only [d1948, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9497 p hg
    simpa only [d1948, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9499 (p : Pattern) (guard : d1949 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9493 p hg
    simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9498 p hg
    simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9500 (p : Pattern) (guard : d1950 p = 1) : d16 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9489 p hg
    simpa only [d1950, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9499 p hg
    simpa only [d1950, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9501 (p : Pattern) (guard : d1954 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare9502 (p : Pattern) (guard : d1955 p = 1) : d328 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9500 p hg
    simpa only [d1955, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9501 p hg
    simpa only [d1955, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9503 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9483 p hg
    simpa only [d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9504 (p : Pattern) (guard : d1945 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9503 p hg
    simpa only [d1945, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9492 p hg
    simpa only [d1945, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9505 (p : Pattern) (guard : d1943 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d1943, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9506 (p : Pattern) (guard : d1944 p = 1) : d6 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9483 p hg
    simpa only [d1944, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1944, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9507 (p : Pattern) (guard : d1943 p = 1) : d4 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d1943, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1943, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9508 (p : Pattern) (guard : d1947 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9507 p hg
    simpa only [d1947, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9509 (p : Pattern) (guard : d1948 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9506 p hg
    simpa only [d1948, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9508 p hg
    simpa only [d1948, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9510 (p : Pattern) (guard : d1949 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9504 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9509 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9511 (p : Pattern) (guard : d1944 p = 1) : d6 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d1944, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1944, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9512 (p : Pattern) (guard : d1948 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9511 p hg
    simpa only [d1948, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9508 p hg
    simpa only [d1948, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9513 (p : Pattern) (guard : d985 p = 1) : d1 p ≤ (0 : Int) + d2 p := by
  change (1 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9514 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9513 p hg
    simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9515 (p : Pattern) (guard : d1947 p = 1) : d12 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9496 p hg
    simpa only [d1947, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9514 p hg
    simpa only [d1947, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9516 (p : Pattern) (guard : d1293 p = 1) : d10 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9513 p hg
    simpa only [d1293, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1293, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9517 (p : Pattern) (guard : d1951 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9516 p hg
    simpa only [d1951, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9518 (p : Pattern) (guard : d1952 p = 1) : d14 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9515 p hg
    simpa only [d1952, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9517 p hg
    simpa only [d1952, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9519 (p : Pattern) (guard : d1953 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9512 p hg
    simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9518 p hg
    simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
