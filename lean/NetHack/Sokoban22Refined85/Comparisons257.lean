/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons256
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35980 (p : Pattern) (guard : d1 p = 1) : d3584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35979 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35981 (p : Pattern) (guard : d1 p = 1) : d3585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35982 (p : Pattern) (guard : d8084 p = 1) : d1715 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8084, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d8084, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35983 (p : Pattern) (guard : d8085 p = 1) : d3586 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35981 p hg
    simpa only [d8085, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35982 p hg
    simpa only [d8085, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35984 (p : Pattern) (guard : d8086 p = 1) : d3587 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35980 p hg
    simpa only [d8086, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35983 p hg
    simpa only [d8086, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35985 (p : Pattern) (guard : d8091 p = 1) : d3588 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35984 p hg
    simpa only [d8091, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35986 (p : Pattern) (guard : d8092 p = 1) : d3589 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35978 p hg
    simpa only [d8092, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35985 p hg
    simpa only [d8092, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35987 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35988 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35989 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35990 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35991 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35988 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35992 (p : Pattern) (guard : d8084 p = 1) : d3577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8084, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35993 (p : Pattern) (guard : d8085 p = 1) : d3578 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8085, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35992 p hg
    simpa only [d8085, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35994 (p : Pattern) (guard : d5847 p = 1) : d3579 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d5847, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35995 (p : Pattern) (guard : d8089 p = 1) : d3580 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8089, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35994 p hg
    simpa only [d8089, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35996 (p : Pattern) (guard : d8090 p = 1) : d3581 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35993 p hg
    simpa only [d8090, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35995 p hg
    simpa only [d8090, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35997 (p : Pattern) (guard : d8091 p = 1) : d3582 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35991 p hg
    simpa only [d8091, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d8091, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35998 (p : Pattern) (guard : d8084 p = 1) : d364 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35999 (p : Pattern) (guard : d8085 p = 1) : d3590 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d8085, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35998 p hg
    simpa only [d8085, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36000 (p : Pattern) (guard : d8084 p = 1) : d3591 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d8084, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36001 (p : Pattern) (guard : d5847 p = 1) : d364 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36002 (p : Pattern) (guard : d8089 p = 1) : d3592 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36000 p hg
    simpa only [d8089, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36001 p hg
    simpa only [d8089, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36003 (p : Pattern) (guard : d8090 p = 1) : d3593 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35999 p hg
    simpa only [d8090, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36002 p hg
    simpa only [d8090, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36004 (p : Pattern) (guard : d8095 p = 1) : d3594 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36003 p hg
    simpa only [d8095, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36005 (p : Pattern) (guard : d8096 p = 1) : d3595 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35997 p hg
    simpa only [d8096, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36004 p hg
    simpa only [d8096, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36006 (p : Pattern) (guard : d8097 p = 1) : d3596 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35986 p hg
    simpa only [d8097, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36005 p hg
    simpa only [d8097, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36007 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35887 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36008 (p : Pattern) (guard : d8091 p = 1) : d3582 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36007 p hg
    simpa only [d8091, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d8091, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36009 (p : Pattern) (guard : d8084 p = 1) : d327 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36010 (p : Pattern) (guard : d8085 p = 1) : d3597 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d8085, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36009 p hg
    simpa only [d8085, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36011 (p : Pattern) (guard : d5847 p = 1) : d327 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36012 (p : Pattern) (guard : d8089 p = 1) : d327 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36009 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36011 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36013 (p : Pattern) (guard : d8090 p = 1) : d3598 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36010 p hg
    simpa only [d8090, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36012 p hg
    simpa only [d8090, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36014 (p : Pattern) (guard : d8095 p = 1) : d3599 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36013 p hg
    simpa only [d8095, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36015 (p : Pattern) (guard : d8096 p = 1) : d3600 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36008 p hg
    simpa only [d8096, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36014 p hg
    simpa only [d8096, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36016 (p : Pattern) (guard : d5847 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36017 (p : Pattern) (guard : d8089 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36018 (p : Pattern) (guard : d8090 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35915 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36019 (p : Pattern) (guard : d5847 p = 1) : d3601 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d5847, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36020 (p : Pattern) (guard : d8089 p = 1) : d3602 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8089, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36019 p hg
    simpa only [d8089, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36021 (p : Pattern) (guard : d5854 p = 1) : d3603 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35920 p hg
    simpa only [d5854, d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17223 p hg
    simpa only [d5854, d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36022 (p : Pattern) (guard : d8094 p = 1) : d3604 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36020 p hg
    simpa only [d8094, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36021 p hg
    simpa only [d8094, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36023 (p : Pattern) (guard : d8095 p = 1) : d3605 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36018 p hg
    simpa only [d8095, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36022 p hg
    simpa only [d8095, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36024 (p : Pattern) (guard : d8101 p = 1) : d3606 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36023 p hg
    simpa only [d8101, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36025 (p : Pattern) (guard : d8102 p = 1) : d3607 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36015 p hg
    simpa only [d8102, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36024 p hg
    simpa only [d8102, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36026 (p : Pattern) (guard : d8103 p = 1) : d3608 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36006 p hg
    simpa only [d8103, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36025 p hg
    simpa only [d8103, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36027 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35903 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36028 (p : Pattern) (guard : d8091 p = 1) : d3582 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36027 p hg
    simpa only [d8091, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d8091, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36029 (p : Pattern) (guard : d8096 p = 1) : d3609 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36028 p hg
    simpa only [d8096, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36030 (p : Pattern) (guard : d8102 p = 1) : d3610 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36029 p hg
    simpa only [d8102, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36024 p hg
    simpa only [d8102, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36031 (p : Pattern) (guard : d5847 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36032 (p : Pattern) (guard : d8089 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35951 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36031 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36033 (p : Pattern) (guard : d8090 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35952 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36032 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36034 (p : Pattern) (guard : d8089 p = 1) : d3566 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35951 p hg
    simpa only [d8089, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35956 p hg
    simpa only [d8089, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36035 (p : Pattern) (guard : d5854 p = 1) : d356 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35956 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36036 (p : Pattern) (guard : d8094 p = 1) : d3567 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36034 p hg
    simpa only [d8094, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36035 p hg
    simpa only [d8094, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36037 (p : Pattern) (guard : d8095 p = 1) : d3568 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36033 p hg
    simpa only [d8095, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36036 p hg
    simpa only [d8095, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36038 (p : Pattern) (guard : d8101 p = 1) : d3611 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36037 p hg
    simpa only [d8101, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36039 (p : Pattern) (guard : d8107 p = 1) : d3612 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36038 p hg
    simpa only [d8107, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36040 (p : Pattern) (guard : d8108 p = 1) : d3613 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36030 p hg
    simpa only [d8108, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36039 p hg
    simpa only [d8108, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36041 (p : Pattern) (guard : d8109 p = 1) : d3614 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36026 p hg
    simpa only [d8109, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36040 p hg
    simpa only [d8109, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36042 (p : Pattern) (guard : d8110 p = 1) : d3615 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35969 p hg
    simpa only [d8110, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36041 p hg
    simpa only [d8110, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36043 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (0 : Int) + d378 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare779 p hg
    simpa only [d1785, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d1785, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36044 (p : Pattern) (guard : d1 p = 1) : d3616 p ≤ (0 : Int) + d379 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3616, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36043 p hg
    simpa only [d3616, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3616, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34460 p hg
    simpa only [d3616, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36045 (p : Pattern) (guard : d1 p = 1) : d3617 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36044 p hg
    simpa only [d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36046 (p : Pattern) (guard : d1 p = 1) : d3618 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36045 p hg
    simpa only [d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35988 p hg
    simpa only [d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36047 (p : Pattern) (guard : d1 p = 1) : d3544 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36048 (p : Pattern) (guard : d8086 p = 1) : d3545 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36047 p hg
    simpa only [d8086, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35891 p hg
    simpa only [d8086, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36049 (p : Pattern) (guard : d8087 p = 1) : d3619 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36046 p hg
    simpa only [d8087, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36048 p hg
    simpa only [d8087, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36050 (p : Pattern) (guard : d1 p = 1) : d3548 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36051 (p : Pattern) (guard : d8086 p = 1) : d3549 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36050 p hg
    simpa only [d8086, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35896 p hg
    simpa only [d8086, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36052 (p : Pattern) (guard : d8091 p = 1) : d3550 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36051 p hg
    simpa only [d8091, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36053 (p : Pattern) (guard : d8092 p = 1) : d3620 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36049 p hg
    simpa only [d8092, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36052 p hg
    simpa only [d8092, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36054 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36055 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36054 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36056 (p : Pattern) (guard : d8084 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36057 (p : Pattern) (guard : d8085 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36058 (p : Pattern) (guard : d8086 p = 1) : d30 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36055 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36057 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36059 (p : Pattern) (guard : d8084 p = 1) : d3585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8084, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36060 (p : Pattern) (guard : d8085 p = 1) : d3621 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8085, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36059 p hg
    simpa only [d8085, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36061 (p : Pattern) (guard : d5847 p = 1) : d3585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d5847, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36062 (p : Pattern) (guard : d8089 p = 1) : d3585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36059 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36061 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36063 (p : Pattern) (guard : d8090 p = 1) : d3622 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36060 p hg
    simpa only [d8090, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36062 p hg
    simpa only [d8090, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36064 (p : Pattern) (guard : d8091 p = 1) : d3623 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36058 p hg
    simpa only [d8091, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36063 p hg
    simpa only [d8091, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36065 (p : Pattern) (guard : d8084 p = 1) : d3624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8084, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36066 (p : Pattern) (guard : d8085 p = 1) : d3625 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8085, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36065 p hg
    simpa only [d8085, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36067 (p : Pattern) (guard : d5847 p = 1) : d3624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d5847, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36068 (p : Pattern) (guard : d8089 p = 1) : d3624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36065 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36067 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36069 (p : Pattern) (guard : d8090 p = 1) : d3626 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36066 p hg
    simpa only [d8090, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36068 p hg
    simpa only [d8090, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36070 (p : Pattern) (guard : d8095 p = 1) : d3627 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36069 p hg
    simpa only [d8095, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36071 (p : Pattern) (guard : d8096 p = 1) : d3628 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36064 p hg
    simpa only [d8096, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36070 p hg
    simpa only [d8096, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36072 (p : Pattern) (guard : d8097 p = 1) : d3629 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36053 p hg
    simpa only [d8097, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36071 p hg
    simpa only [d8097, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36073 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare790 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36074 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36073 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36075 (p : Pattern) (guard : d8086 p = 1) : d17 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36074 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35915 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36076 (p : Pattern) (guard : d8091 p = 1) : d3558 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36075 p hg
    simpa only [d8091, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35922 p hg
    simpa only [d8091, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36077 (p : Pattern) (guard : d8096 p = 1) : d3563 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36076 p hg
    simpa only [d8096, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35929 p hg
    simpa only [d8096, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36078 (p : Pattern) (guard : d8085 p = 1) : d23 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35949 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35951 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36079 (p : Pattern) (guard : d8090 p = 1) : d23 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36078 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36032 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36080 (p : Pattern) (guard : d8095 p = 1) : d3568 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36079 p hg
    simpa only [d8095, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36036 p hg
    simpa only [d8095, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36081 (p : Pattern) (guard : d8089 p = 1) : d3570 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35951 p hg
    simpa only [d8089, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35962 p hg
    simpa only [d8089, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36082 (p : Pattern) (guard : d5854 p = 1) : d3569 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35962 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29260 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36083 (p : Pattern) (guard : d8094 p = 1) : d3571 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36081 p hg
    simpa only [d8094, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36082 p hg
    simpa only [d8094, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36084 (p : Pattern) (guard : d8100 p = 1) : d3572 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36083 p hg
    simpa only [d8100, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36085 (p : Pattern) (guard : d8101 p = 1) : d3573 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36080 p hg
    simpa only [d8101, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36084 p hg
    simpa only [d8101, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36086 (p : Pattern) (guard : d8102 p = 1) : d3630 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36077 p hg
    simpa only [d8102, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36085 p hg
    simpa only [d8102, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36087 (p : Pattern) (guard : d8103 p = 1) : d3631 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36072 p hg
    simpa only [d8103, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36086 p hg
    simpa only [d8103, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36088 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare36089 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36088 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36090 (p : Pattern) (guard : d8084 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36091 (p : Pattern) (guard : d8085 p = 1) : d57 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36089 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36090 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36092 (p : Pattern) (guard : d5847 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36093 (p : Pattern) (guard : d8089 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36090 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36092 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36094 (p : Pattern) (guard : d8090 p = 1) : d57 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36091 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36093 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36095 (p : Pattern) (guard : d5847 p = 1) : d329 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36096 (p : Pattern) (guard : d8089 p = 1) : d3632 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36090 p hg
    simpa only [d8089, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36095 p hg
    simpa only [d8089, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36097 (p : Pattern) (guard : d5854 p = 1) : d329 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36095 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36098 (p : Pattern) (guard : d8094 p = 1) : d3633 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36096 p hg
    simpa only [d8094, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36097 p hg
    simpa only [d8094, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36099 (p : Pattern) (guard : d8095 p = 1) : d3634 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36094 p hg
    simpa only [d8095, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36098 p hg
    simpa only [d8095, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36100 (p : Pattern) (guard : d8100 p = 1) : d3635 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36098 p hg
    simpa only [d8100, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36101 (p : Pattern) (guard : d8101 p = 1) : d3636 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36099 p hg
    simpa only [d8101, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36100 p hg
    simpa only [d8101, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36102 (p : Pattern) (guard : d8102 p = 1) : d3637 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35930 p hg
    simpa only [d8102, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36101 p hg
    simpa only [d8102, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36103 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (0 : Int) + d39 p := by
  omega
theorem compare36104 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36103 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36105 (p : Pattern) (guard : d8084 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36106 (p : Pattern) (guard : d8085 p = 1) : d39 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36104 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36105 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36107 (p : Pattern) (guard : d5847 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36108 (p : Pattern) (guard : d8089 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36105 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36107 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36109 (p : Pattern) (guard : d8090 p = 1) : d39 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36106 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36108 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36110 (p : Pattern) (guard : d8089 p = 1) : d3597 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36105 p hg
    simpa only [d8089, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36011 p hg
    simpa only [d8089, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36111 (p : Pattern) (guard : d5854 p = 1) : d327 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36011 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36112 (p : Pattern) (guard : d8094 p = 1) : d3598 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36110 p hg
    simpa only [d8094, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36111 p hg
    simpa only [d8094, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36113 (p : Pattern) (guard : d8095 p = 1) : d3638 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36109 p hg
    simpa only [d8095, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36112 p hg
    simpa only [d8095, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36114 (p : Pattern) (guard : d8100 p = 1) : d3599 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36112 p hg
    simpa only [d8100, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36115 (p : Pattern) (guard : d8101 p = 1) : d3639 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36113 p hg
    simpa only [d8101, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36114 p hg
    simpa only [d8101, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36116 (p : Pattern) (guard : d8107 p = 1) : d3640 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36115 p hg
    simpa only [d8107, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36117 (p : Pattern) (guard : d8108 p = 1) : d3641 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36102 p hg
    simpa only [d8108, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36116 p hg
    simpa only [d8108, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36118 (p : Pattern) (guard : d8109 p = 1) : d3642 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36087 p hg
    simpa only [d8109, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36117 p hg
    simpa only [d8109, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36119 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
