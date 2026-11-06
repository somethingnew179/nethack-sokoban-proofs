/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons273
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38360 (p : Pattern) (guard : d5843 p = 1) : d1693 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38361 (p : Pattern) (guard : d5847 p = 1) : d1694 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38360 p hg
    simpa only [d5847, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38362 (p : Pattern) (guard : d8089 p = 1) : d1694 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38358 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38361 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38363 (p : Pattern) (guard : d8090 p = 1) : d1696 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38359 p hg
    simpa only [d8090, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38362 p hg
    simpa only [d8090, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38364 (p : Pattern) (guard : d8095 p = 1) : d1697 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38363 p hg
    simpa only [d8095, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38365 (p : Pattern) (guard : d8096 p = 1) : d1698 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38356 p hg
    simpa only [d8096, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38364 p hg
    simpa only [d8096, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38366 (p : Pattern) (guard : d8097 p = 1) : d1699 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38355 p hg
    simpa only [d8097, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38365 p hg
    simpa only [d8097, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38367 (p : Pattern) (guard : d8098 p = 1) : d1700 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38350 p hg
    simpa only [d8098, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38366 p hg
    simpa only [d8098, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38368 (p : Pattern) (guard : d8087 p = 1) : d15 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34374 p hg
    simpa only [d8087, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38369 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38370 (p : Pattern) (guard : d8086 p = 1) : d1686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38369 p hg
    simpa only [d8086, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38346 p hg
    simpa only [d8086, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38371 (p : Pattern) (guard : d8091 p = 1) : d1687 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38370 p hg
    simpa only [d8091, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38372 (p : Pattern) (guard : d8092 p = 1) : d1692 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38368 p hg
    simpa only [d8092, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38371 p hg
    simpa only [d8092, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38373 (p : Pattern) (guard : d8091 p = 1) : d19 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34382 p hg
    simpa only [d8091, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38374 (p : Pattern) (guard : d8096 p = 1) : d1698 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38373 p hg
    simpa only [d8096, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38364 p hg
    simpa only [d8096, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38375 (p : Pattern) (guard : d8097 p = 1) : d1699 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38372 p hg
    simpa only [d8097, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38374 p hg
    simpa only [d8097, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38376 (p : Pattern) (guard : d8091 p = 1) : d25 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34391 p hg
    simpa only [d8091, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38377 (p : Pattern) (guard : d1 p = 1) : d1701 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38378 (p : Pattern) (guard : d8084 p = 1) : d1702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38377 p hg
    simpa only [d8084, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d8084, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38379 (p : Pattern) (guard : d8085 p = 1) : d1703 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d8085, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38378 p hg
    simpa only [d8085, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38380 (p : Pattern) (guard : d5843 p = 1) : d1701 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38381 (p : Pattern) (guard : d5847 p = 1) : d1702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38380 p hg
    simpa only [d5847, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38382 (p : Pattern) (guard : d8089 p = 1) : d1702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38378 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38381 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38383 (p : Pattern) (guard : d8090 p = 1) : d1704 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38379 p hg
    simpa only [d8090, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38382 p hg
    simpa only [d8090, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38384 (p : Pattern) (guard : d8095 p = 1) : d1705 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38383 p hg
    simpa only [d8095, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38385 (p : Pattern) (guard : d8096 p = 1) : d1706 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38376 p hg
    simpa only [d8096, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38384 p hg
    simpa only [d8096, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38386 (p : Pattern) (guard : d8102 p = 1) : d1707 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38385 p hg
    simpa only [d8102, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38387 (p : Pattern) (guard : d8103 p = 1) : d1708 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38375 p hg
    simpa only [d8103, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38386 p hg
    simpa only [d8103, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38388 (p : Pattern) (guard : d8104 p = 1) : d1709 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38367 p hg
    simpa only [d8104, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38387 p hg
    simpa only [d8104, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38389 (p : Pattern) (guard : d8087 p = 1) : d15 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34405 p hg
    simpa only [d8087, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38390 (p : Pattern) (guard : d1 p = 1) : d1710 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38391 (p : Pattern) (guard : d1 p = 1) : d1711 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38390 p hg
    simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1639 p hg
    simpa only [d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38392 (p : Pattern) (guard : d1 p = 1) : d1712 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38391 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38393 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38394 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38393 p hg
    simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38395 (p : Pattern) (guard : d8085 p = 1) : d1716 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38394 p hg
    simpa only [d8085, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35982 p hg
    simpa only [d8085, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38396 (p : Pattern) (guard : d8086 p = 1) : d1717 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38392 p hg
    simpa only [d8086, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38395 p hg
    simpa only [d8086, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38397 (p : Pattern) (guard : d8091 p = 1) : d1718 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38396 p hg
    simpa only [d8091, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38398 (p : Pattern) (guard : d8092 p = 1) : d1719 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38389 p hg
    simpa only [d8092, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38397 p hg
    simpa only [d8092, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38399 (p : Pattern) (guard : d8085 p = 1) : d1720 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d8085, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35998 p hg
    simpa only [d8085, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38400 (p : Pattern) (guard : d1 p = 1) : d1721 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38401 (p : Pattern) (guard : d8084 p = 1) : d1722 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38400 p hg
    simpa only [d8084, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38402 (p : Pattern) (guard : d8089 p = 1) : d1723 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38401 p hg
    simpa only [d8089, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36001 p hg
    simpa only [d8089, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38403 (p : Pattern) (guard : d8090 p = 1) : d1724 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38399 p hg
    simpa only [d8090, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38402 p hg
    simpa only [d8090, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38404 (p : Pattern) (guard : d8095 p = 1) : d1725 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38403 p hg
    simpa only [d8095, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38405 (p : Pattern) (guard : d8096 p = 1) : d1726 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34465 p hg
    simpa only [d8096, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38404 p hg
    simpa only [d8096, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38406 (p : Pattern) (guard : d8097 p = 1) : d1727 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38398 p hg
    simpa only [d8097, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38405 p hg
    simpa only [d8097, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38407 (p : Pattern) (guard : d8085 p = 1) : d1728 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d8085, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36009 p hg
    simpa only [d8085, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38408 (p : Pattern) (guard : d8090 p = 1) : d1729 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38407 p hg
    simpa only [d8090, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36012 p hg
    simpa only [d8090, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38409 (p : Pattern) (guard : d8095 p = 1) : d1730 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38408 p hg
    simpa only [d8095, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38410 (p : Pattern) (guard : d8096 p = 1) : d1731 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34345 p hg
    simpa only [d8096, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38409 p hg
    simpa only [d8096, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38411 (p : Pattern) (guard : d8101 p = 1) : d1732 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34368 p hg
    simpa only [d8101, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38412 (p : Pattern) (guard : d8102 p = 1) : d1733 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38410 p hg
    simpa only [d8102, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38411 p hg
    simpa only [d8102, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38413 (p : Pattern) (guard : d8103 p = 1) : d1734 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38406 p hg
    simpa only [d8103, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38412 p hg
    simpa only [d8103, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38414 (p : Pattern) (guard : d8096 p = 1) : d1735 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34353 p hg
    simpa only [d8096, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38415 (p : Pattern) (guard : d8102 p = 1) : d1736 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38414 p hg
    simpa only [d8102, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38411 p hg
    simpa only [d8102, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38416 (p : Pattern) (guard : d8101 p = 1) : d527 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34397 p hg
    simpa only [d8101, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38417 (p : Pattern) (guard : d8107 p = 1) : d528 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38416 p hg
    simpa only [d8107, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38418 (p : Pattern) (guard : d8108 p = 1) : d1737 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38415 p hg
    simpa only [d8108, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38417 p hg
    simpa only [d8108, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38419 (p : Pattern) (guard : d8109 p = 1) : d1738 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38413 p hg
    simpa only [d8109, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38418 p hg
    simpa only [d8109, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38420 (p : Pattern) (guard : d8110 p = 1) : d1739 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38388 p hg
    simpa only [d8110, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38419 p hg
    simpa only [d8110, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38421 (p : Pattern) (guard : d8086 p = 1) : d335 p ≤ (0 : Int) + d335 p := by
  omega
theorem compare38422 (p : Pattern) (guard : d8087 p = 1) : d1740 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34463 p hg
    simpa only [d8087, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38421 p hg
    simpa only [d8087, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38423 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38424 (p : Pattern) (guard : d8086 p = 1) : d1686 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38423 p hg
    simpa only [d8086, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38346 p hg
    simpa only [d8086, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38425 (p : Pattern) (guard : d8091 p = 1) : d1687 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38424 p hg
    simpa only [d8091, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38426 (p : Pattern) (guard : d8092 p = 1) : d1741 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38422 p hg
    simpa only [d8092, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38425 p hg
    simpa only [d8092, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38427 (p : Pattern) (guard : d8091 p = 1) : d32 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34470 p hg
    simpa only [d8091, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38428 (p : Pattern) (guard : d1 p = 1) : d1742 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38429 (p : Pattern) (guard : d8084 p = 1) : d1743 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38428 p hg
    simpa only [d8084, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38430 (p : Pattern) (guard : d8085 p = 1) : d1744 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d8085, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38429 p hg
    simpa only [d8085, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38431 (p : Pattern) (guard : d5843 p = 1) : d1742 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38432 (p : Pattern) (guard : d5847 p = 1) : d1743 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38431 p hg
    simpa only [d5847, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38433 (p : Pattern) (guard : d8089 p = 1) : d1743 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38429 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38432 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38434 (p : Pattern) (guard : d8090 p = 1) : d1745 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38430 p hg
    simpa only [d8090, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38433 p hg
    simpa only [d8090, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38435 (p : Pattern) (guard : d8095 p = 1) : d1746 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38434 p hg
    simpa only [d8095, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38436 (p : Pattern) (guard : d8096 p = 1) : d1747 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38427 p hg
    simpa only [d8096, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38435 p hg
    simpa only [d8096, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38437 (p : Pattern) (guard : d8097 p = 1) : d1748 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38426 p hg
    simpa only [d8097, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38436 p hg
    simpa only [d8097, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38438 (p : Pattern) (guard : d8091 p = 1) : d19 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34482 p hg
    simpa only [d8091, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38439 (p : Pattern) (guard : d8096 p = 1) : d1698 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38438 p hg
    simpa only [d8096, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38364 p hg
    simpa only [d8096, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38440 (p : Pattern) (guard : d8095 p = 1) : d25 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34486 p hg
    simpa only [d8095, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38441 (p : Pattern) (guard : d8089 p = 1) : d1703 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d8089, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38381 p hg
    simpa only [d8089, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38442 (p : Pattern) (guard : d5854 p = 1) : d1702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38381 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17112 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38443 (p : Pattern) (guard : d8094 p = 1) : d1704 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38441 p hg
    simpa only [d8094, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38442 p hg
    simpa only [d8094, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38444 (p : Pattern) (guard : d8100 p = 1) : d1705 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38443 p hg
    simpa only [d8100, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38445 (p : Pattern) (guard : d8101 p = 1) : d1706 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38440 p hg
    simpa only [d8101, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38444 p hg
    simpa only [d8101, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38446 (p : Pattern) (guard : d8102 p = 1) : d1749 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38439 p hg
    simpa only [d8102, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38445 p hg
    simpa only [d8102, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38447 (p : Pattern) (guard : d8103 p = 1) : d1750 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38437 p hg
    simpa only [d8103, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38446 p hg
    simpa only [d8103, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38448 (p : Pattern) (guard : d8095 p = 1) : d59 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34500 p hg
    simpa only [d8095, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38449 (p : Pattern) (guard : d8089 p = 1) : d1751 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34495 p hg
    simpa only [d8089, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36095 p hg
    simpa only [d8089, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38450 (p : Pattern) (guard : d8094 p = 1) : d1752 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38449 p hg
    simpa only [d8094, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36097 p hg
    simpa only [d8094, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38451 (p : Pattern) (guard : d8100 p = 1) : d1753 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38450 p hg
    simpa only [d8100, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38452 (p : Pattern) (guard : d8101 p = 1) : d1754 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38448 p hg
    simpa only [d8101, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38451 p hg
    simpa only [d8101, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38453 (p : Pattern) (guard : d8102 p = 1) : d1755 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38365 p hg
    simpa only [d8102, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38452 p hg
    simpa only [d8102, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38454 (p : Pattern) (guard : d8095 p = 1) : d41 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34509 p hg
    simpa only [d8095, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38455 (p : Pattern) (guard : d8089 p = 1) : d1728 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34432 p hg
    simpa only [d8089, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36011 p hg
    simpa only [d8089, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38456 (p : Pattern) (guard : d8094 p = 1) : d1729 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38455 p hg
    simpa only [d8094, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36111 p hg
    simpa only [d8094, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38457 (p : Pattern) (guard : d8100 p = 1) : d1730 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38456 p hg
    simpa only [d8100, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38458 (p : Pattern) (guard : d8101 p = 1) : d1756 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38454 p hg
    simpa only [d8101, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38459 (p : Pattern) (guard : d8107 p = 1) : d1757 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38458 p hg
    simpa only [d8107, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38460 (p : Pattern) (guard : d8108 p = 1) : d1758 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38453 p hg
    simpa only [d8108, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38459 p hg
    simpa only [d8108, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38461 (p : Pattern) (guard : d8109 p = 1) : d1759 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38447 p hg
    simpa only [d8109, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38460 p hg
    simpa only [d8109, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38462 (p : Pattern) (guard : d8096 p = 1) : d1726 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34748 p hg
    simpa only [d8096, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38404 p hg
    simpa only [d8096, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38463 (p : Pattern) (guard : d8095 p = 1) : d32 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34524 p hg
    simpa only [d8095, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38464 (p : Pattern) (guard : d8101 p = 1) : d1760 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38463 p hg
    simpa only [d8101, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38465 (p : Pattern) (guard : d8102 p = 1) : d1761 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38462 p hg
    simpa only [d8102, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38464 p hg
    simpa only [d8102, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38466 (p : Pattern) (guard : d8106 p = 1) : d527 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34489 p hg
    simpa only [d8106, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38467 (p : Pattern) (guard : d8107 p = 1) : d1762 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38411 p hg
    simpa only [d8107, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38466 p hg
    simpa only [d8107, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38468 (p : Pattern) (guard : d8108 p = 1) : d1763 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38465 p hg
    simpa only [d8108, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38467 p hg
    simpa only [d8108, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38469 (p : Pattern) (guard : d8106 p = 1) : d277 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34504 p hg
    simpa only [d8106, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38470 (p : Pattern) (guard : d8107 p = 1) : d1764 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38411 p hg
    simpa only [d8107, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38469 p hg
    simpa only [d8107, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38471 (p : Pattern) (guard : d8106 p = 1) : d538 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d8106, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38472 (p : Pattern) (guard : d8112 p = 1) : d539 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38471 p hg
    simpa only [d8112, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38473 (p : Pattern) (guard : d8113 p = 1) : d1765 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38470 p hg
    simpa only [d8113, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38472 p hg
    simpa only [d8113, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38474 (p : Pattern) (guard : d8114 p = 1) : d1766 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38468 p hg
    simpa only [d8114, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38473 p hg
    simpa only [d8114, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38475 (p : Pattern) (guard : d8115 p = 1) : d1767 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38461 p hg
    simpa only [d8115, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38474 p hg
    simpa only [d8115, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38476 (p : Pattern) (guard : d8116 p = 1) : d1768 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38420 p hg
    simpa only [d8116, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38475 p hg
    simpa only [d8116, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38477 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38478 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38477 p hg
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38479 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38480 (p : Pattern) (guard : d8084 p = 1) : d1770 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38477 p hg
    simpa only [d8084, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38481 (p : Pattern) (guard : d8085 p = 1) : d1770 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38482 (p : Pattern) (guard : d8086 p = 1) : d1772 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38479 p hg
    simpa only [d8086, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38481 p hg
    simpa only [d8086, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38483 (p : Pattern) (guard : d8091 p = 1) : d1773 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38482 p hg
    simpa only [d8091, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38484 (p : Pattern) (guard : d8092 p = 1) : d1774 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38368 p hg
    simpa only [d8092, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38483 p hg
    simpa only [d8092, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38485 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38486 (p : Pattern) (guard : d8084 p = 1) : d1776 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38485 p hg
    simpa only [d8084, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38487 (p : Pattern) (guard : d8085 p = 1) : d1777 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d8085, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38486 p hg
    simpa only [d8085, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38488 (p : Pattern) (guard : d5843 p = 1) : d1778 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38489 (p : Pattern) (guard : d5847 p = 1) : d1779 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38488 p hg
    simpa only [d5847, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38490 (p : Pattern) (guard : d8089 p = 1) : d1780 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8089, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38489 p hg
    simpa only [d8089, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38491 (p : Pattern) (guard : d8090 p = 1) : d1781 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38487 p hg
    simpa only [d8090, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38490 p hg
    simpa only [d8090, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38492 (p : Pattern) (guard : d8095 p = 1) : d1782 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38491 p hg
    simpa only [d8095, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38493 (p : Pattern) (guard : d8096 p = 1) : d1783 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34748 p hg
    simpa only [d8096, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38492 p hg
    simpa only [d8096, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38494 (p : Pattern) (guard : d8097 p = 1) : d1784 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38484 p hg
    simpa only [d8097, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38493 p hg
    simpa only [d8097, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38495 (p : Pattern) (guard : d5843 p = 1) : d1785 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38496 (p : Pattern) (guard : d5847 p = 1) : d1786 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38495 p hg
    simpa only [d5847, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38497 (p : Pattern) (guard : d8089 p = 1) : d1787 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8089, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38496 p hg
    simpa only [d8089, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38498 (p : Pattern) (guard : d8090 p = 1) : d1788 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38487 p hg
    simpa only [d8090, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38497 p hg
    simpa only [d8090, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38499 (p : Pattern) (guard : d8095 p = 1) : d1789 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d8095, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
