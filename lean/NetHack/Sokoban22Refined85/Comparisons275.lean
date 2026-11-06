/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons274
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38500 (p : Pattern) (guard : d8096 p = 1) : d1790 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34465 p hg
    simpa only [d8096, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38499 p hg
    simpa only [d8096, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38501 (p : Pattern) (guard : d5843 p = 1) : d1791 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38502 (p : Pattern) (guard : d5847 p = 1) : d1792 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38501 p hg
    simpa only [d5847, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38503 (p : Pattern) (guard : d8089 p = 1) : d1793 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8089, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38502 p hg
    simpa only [d8089, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38504 (p : Pattern) (guard : d5843 p = 1) : d1794 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38505 (p : Pattern) (guard : d5847 p = 1) : d1795 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38504 p hg
    simpa only [d5847, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38506 (p : Pattern) (guard : d5854 p = 1) : d1796 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38505 p hg
    simpa only [d5854, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17223 p hg
    simpa only [d5854, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38507 (p : Pattern) (guard : d8094 p = 1) : d1797 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38503 p hg
    simpa only [d8094, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38506 p hg
    simpa only [d8094, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38508 (p : Pattern) (guard : d8100 p = 1) : d1798 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38507 p hg
    simpa only [d8100, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38509 (p : Pattern) (guard : d8101 p = 1) : d1799 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34368 p hg
    simpa only [d8101, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38508 p hg
    simpa only [d8101, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38510 (p : Pattern) (guard : d8102 p = 1) : d1800 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38500 p hg
    simpa only [d8102, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38509 p hg
    simpa only [d8102, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38511 (p : Pattern) (guard : d8103 p = 1) : d1801 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38494 p hg
    simpa only [d8103, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38510 p hg
    simpa only [d8103, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38512 (p : Pattern) (guard : d8096 p = 1) : d1790 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34345 p hg
    simpa only [d8096, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38499 p hg
    simpa only [d8096, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38513 (p : Pattern) (guard : d8102 p = 1) : d1800 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38512 p hg
    simpa only [d8102, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38509 p hg
    simpa only [d8102, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38514 (p : Pattern) (guard : d8089 p = 1) : d1802 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d8089, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35956 p hg
    simpa only [d8089, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38515 (p : Pattern) (guard : d8094 p = 1) : d1803 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38514 p hg
    simpa only [d8094, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36035 p hg
    simpa only [d8094, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38516 (p : Pattern) (guard : d8100 p = 1) : d1804 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38515 p hg
    simpa only [d8100, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38517 (p : Pattern) (guard : d8101 p = 1) : d1805 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34397 p hg
    simpa only [d8101, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38516 p hg
    simpa only [d8101, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38518 (p : Pattern) (guard : d8107 p = 1) : d1806 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38517 p hg
    simpa only [d8107, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38519 (p : Pattern) (guard : d8108 p = 1) : d1807 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38513 p hg
    simpa only [d8108, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38518 p hg
    simpa only [d8108, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38520 (p : Pattern) (guard : d8109 p = 1) : d1808 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38511 p hg
    simpa only [d8109, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38519 p hg
    simpa only [d8109, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38521 (p : Pattern) (guard : d8091 p = 1) : d32 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34564 p hg
    simpa only [d8091, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38522 (p : Pattern) (guard : d8084 p = 1) : d1711 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38390 p hg
    simpa only [d8084, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35917 p hg
    simpa only [d8084, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38523 (p : Pattern) (guard : d8085 p = 1) : d1712 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d8085, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38522 p hg
    simpa only [d8085, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38524 (p : Pattern) (guard : d8084 p = 1) : d1714 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38393 p hg
    simpa only [d8084, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38525 (p : Pattern) (guard : d8089 p = 1) : d1716 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38524 p hg
    simpa only [d8089, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36189 p hg
    simpa only [d8089, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38526 (p : Pattern) (guard : d8090 p = 1) : d1717 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38523 p hg
    simpa only [d8090, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38525 p hg
    simpa only [d8090, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38527 (p : Pattern) (guard : d8095 p = 1) : d1718 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38526 p hg
    simpa only [d8095, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38528 (p : Pattern) (guard : d8096 p = 1) : d1809 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38521 p hg
    simpa only [d8096, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38529 (p : Pattern) (guard : d8089 p = 1) : d1720 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34421 p hg
    simpa only [d8089, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36001 p hg
    simpa only [d8089, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38530 (p : Pattern) (guard : d5843 p = 1) : d1721 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38531 (p : Pattern) (guard : d5847 p = 1) : d1722 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38530 p hg
    simpa only [d5847, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38532 (p : Pattern) (guard : d5854 p = 1) : d1723 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38531 p hg
    simpa only [d5854, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5854, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38533 (p : Pattern) (guard : d8094 p = 1) : d1724 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38529 p hg
    simpa only [d8094, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38532 p hg
    simpa only [d8094, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38534 (p : Pattern) (guard : d8100 p = 1) : d1725 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38533 p hg
    simpa only [d8100, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38535 (p : Pattern) (guard : d8101 p = 1) : d1810 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34427 p hg
    simpa only [d8101, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38536 (p : Pattern) (guard : d8102 p = 1) : d1811 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38528 p hg
    simpa only [d8102, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38535 p hg
    simpa only [d8102, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38537 (p : Pattern) (guard : d8101 p = 1) : d1756 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34438 p hg
    simpa only [d8101, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38538 (p : Pattern) (guard : d8107 p = 1) : d1757 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38537 p hg
    simpa only [d8107, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38539 (p : Pattern) (guard : d8108 p = 1) : d1812 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38536 p hg
    simpa only [d8108, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38538 p hg
    simpa only [d8108, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38540 (p : Pattern) (guard : d8114 p = 1) : d1813 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38539 p hg
    simpa only [d8114, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38541 (p : Pattern) (guard : d8115 p = 1) : d1814 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38520 p hg
    simpa only [d8115, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38540 p hg
    simpa only [d8115, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38542 (p : Pattern) (guard : d8096 p = 1) : d1783 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d8096, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38492 p hg
    simpa only [d8096, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38543 (p : Pattern) (guard : d8095 p = 1) : d32 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34587 p hg
    simpa only [d8095, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38544 (p : Pattern) (guard : d5843 p = 1) : d1710 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38545 (p : Pattern) (guard : d5847 p = 1) : d1711 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38544 p hg
    simpa only [d5847, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38546 (p : Pattern) (guard : d8089 p = 1) : d1712 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8089, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38545 p hg
    simpa only [d8089, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38547 (p : Pattern) (guard : d5843 p = 1) : d1713 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38548 (p : Pattern) (guard : d5847 p = 1) : d1714 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38547 p hg
    simpa only [d5847, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38549 (p : Pattern) (guard : d5854 p = 1) : d1716 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38548 p hg
    simpa only [d5854, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17126 p hg
    simpa only [d5854, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38550 (p : Pattern) (guard : d8094 p = 1) : d1717 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38546 p hg
    simpa only [d8094, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38549 p hg
    simpa only [d8094, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38551 (p : Pattern) (guard : d8100 p = 1) : d1718 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38550 p hg
    simpa only [d8100, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38552 (p : Pattern) (guard : d8101 p = 1) : d1809 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38543 p hg
    simpa only [d8101, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38553 (p : Pattern) (guard : d8102 p = 1) : d1815 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38542 p hg
    simpa only [d8102, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38552 p hg
    simpa only [d8102, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38554 (p : Pattern) (guard : d8095 p = 1) : d19 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34595 p hg
    simpa only [d8095, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38555 (p : Pattern) (guard : d8101 p = 1) : d1799 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38554 p hg
    simpa only [d8101, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38508 p hg
    simpa only [d8101, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38556 (p : Pattern) (guard : d5854 p = 1) : d1802 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d5854, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5854, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38557 (p : Pattern) (guard : d8099 p = 1) : d1803 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38556 p hg
    simpa only [d8099, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d8099, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38558 (p : Pattern) (guard : d8105 p = 1) : d1804 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38557 p hg
    simpa only [d8105, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38559 (p : Pattern) (guard : d8106 p = 1) : d1805 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34489 p hg
    simpa only [d8106, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38558 p hg
    simpa only [d8106, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38560 (p : Pattern) (guard : d8107 p = 1) : d1816 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38555 p hg
    simpa only [d8107, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38559 p hg
    simpa only [d8107, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38561 (p : Pattern) (guard : d8108 p = 1) : d1817 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38553 p hg
    simpa only [d8108, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38560 p hg
    simpa only [d8108, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38562 (p : Pattern) (guard : d5854 p = 1) : d1751 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34498 p hg
    simpa only [d5854, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5854, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38563 (p : Pattern) (guard : d8099 p = 1) : d1752 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38562 p hg
    simpa only [d8099, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d8099, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38564 (p : Pattern) (guard : d8105 p = 1) : d1753 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38563 p hg
    simpa only [d8105, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38565 (p : Pattern) (guard : d8106 p = 1) : d1754 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34504 p hg
    simpa only [d8106, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38564 p hg
    simpa only [d8106, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38566 (p : Pattern) (guard : d8107 p = 1) : d1818 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38509 p hg
    simpa only [d8107, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38565 p hg
    simpa only [d8107, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38567 (p : Pattern) (guard : d5854 p = 1) : d1728 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34435 p hg
    simpa only [d5854, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5854, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38568 (p : Pattern) (guard : d8099 p = 1) : d1729 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38567 p hg
    simpa only [d8099, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d8099, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38569 (p : Pattern) (guard : d8105 p = 1) : d1730 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38568 p hg
    simpa only [d8105, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38570 (p : Pattern) (guard : d8106 p = 1) : d1756 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d8106, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38571 (p : Pattern) (guard : d8112 p = 1) : d1757 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38570 p hg
    simpa only [d8112, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38572 (p : Pattern) (guard : d8113 p = 1) : d1819 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38566 p hg
    simpa only [d8113, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38573 (p : Pattern) (guard : d8114 p = 1) : d1820 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38561 p hg
    simpa only [d8114, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38572 p hg
    simpa only [d8114, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38574 (p : Pattern) (guard : d8107 p = 1) : d1821 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38535 p hg
    simpa only [d8107, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38575 (p : Pattern) (guard : d8113 p = 1) : d1822 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38574 p hg
    simpa only [d8113, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38576 (p : Pattern) (guard : d8119 p = 1) : d1823 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38575 p hg
    simpa only [d8119, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38577 (p : Pattern) (guard : d8120 p = 1) : d1824 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38573 p hg
    simpa only [d8120, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38576 p hg
    simpa only [d8120, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38578 (p : Pattern) (guard : d8121 p = 1) : d1825 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38541 p hg
    simpa only [d8121, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38577 p hg
    simpa only [d8121, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38579 (p : Pattern) (guard : d8122 p = 1) : d1826 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38476 p hg
    simpa only [d8122, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38578 p hg
    simpa only [d8122, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38580 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38581 (p : Pattern) (guard : d8086 p = 1) : d1772 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38580 p hg
    simpa only [d8086, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38481 p hg
    simpa only [d8086, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38582 (p : Pattern) (guard : d8091 p = 1) : d1773 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38581 p hg
    simpa only [d8091, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38583 (p : Pattern) (guard : d8092 p = 1) : d1774 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38351 p hg
    simpa only [d8092, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38582 p hg
    simpa only [d8092, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38584 (p : Pattern) (guard : d8097 p = 1) : d1784 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38583 p hg
    simpa only [d8097, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38542 p hg
    simpa only [d8097, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38585 (p : Pattern) (guard : d8096 p = 1) : d1790 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34748 p hg
    simpa only [d8096, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38499 p hg
    simpa only [d8096, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38586 (p : Pattern) (guard : d8102 p = 1) : d1800 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38585 p hg
    simpa only [d8102, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38555 p hg
    simpa only [d8102, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38587 (p : Pattern) (guard : d8103 p = 1) : d1801 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38584 p hg
    simpa only [d8103, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38586 p hg
    simpa only [d8103, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38588 (p : Pattern) (guard : d8108 p = 1) : d1807 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38510 p hg
    simpa only [d8108, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38518 p hg
    simpa only [d8108, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38589 (p : Pattern) (guard : d8109 p = 1) : d1808 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38587 p hg
    simpa only [d8109, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38588 p hg
    simpa only [d8109, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38590 (p : Pattern) (guard : d8091 p = 1) : d32 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38108 p hg
    simpa only [d8091, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38591 (p : Pattern) (guard : d8096 p = 1) : d1809 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38590 p hg
    simpa only [d8096, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38592 (p : Pattern) (guard : d8102 p = 1) : d1811 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38591 p hg
    simpa only [d8102, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38535 p hg
    simpa only [d8102, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38593 (p : Pattern) (guard : d8108 p = 1) : d1812 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38592 p hg
    simpa only [d8108, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38538 p hg
    simpa only [d8108, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38594 (p : Pattern) (guard : d8114 p = 1) : d1813 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38593 p hg
    simpa only [d8114, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38595 (p : Pattern) (guard : d8115 p = 1) : d1814 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38589 p hg
    simpa only [d8115, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38594 p hg
    simpa only [d8115, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38596 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34620 p hg
    simpa only [d8091, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38597 (p : Pattern) (guard : d8096 p = 1) : d1783 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38596 p hg
    simpa only [d8096, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38492 p hg
    simpa only [d8096, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38598 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38599 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38598 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38600 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38599 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38601 (p : Pattern) (guard : d8095 p = 1) : d32 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38600 p hg
    simpa only [d8095, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38602 (p : Pattern) (guard : d8101 p = 1) : d1809 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38601 p hg
    simpa only [d8101, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38603 (p : Pattern) (guard : d8102 p = 1) : d1815 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38597 p hg
    simpa only [d8102, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38602 p hg
    simpa only [d8102, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38604 (p : Pattern) (guard : d8095 p = 1) : d19 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34627 p hg
    simpa only [d8095, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38605 (p : Pattern) (guard : d8101 p = 1) : d1799 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38604 p hg
    simpa only [d8101, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38508 p hg
    simpa only [d8101, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38606 (p : Pattern) (guard : d8107 p = 1) : d1816 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38605 p hg
    simpa only [d8107, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38559 p hg
    simpa only [d8107, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38607 (p : Pattern) (guard : d8108 p = 1) : d1817 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38603 p hg
    simpa only [d8108, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38606 p hg
    simpa only [d8108, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38608 (p : Pattern) (guard : d8107 p = 1) : d1818 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38555 p hg
    simpa only [d8107, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38565 p hg
    simpa only [d8107, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38609 (p : Pattern) (guard : d8113 p = 1) : d1819 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38608 p hg
    simpa only [d8113, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38610 (p : Pattern) (guard : d8114 p = 1) : d1820 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38607 p hg
    simpa only [d8114, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38609 p hg
    simpa only [d8114, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38611 (p : Pattern) (guard : d8120 p = 1) : d1824 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38610 p hg
    simpa only [d8120, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38576 p hg
    simpa only [d8120, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38612 (p : Pattern) (guard : d8121 p = 1) : d1825 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38595 p hg
    simpa only [d8121, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38611 p hg
    simpa only [d8121, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38613 (p : Pattern) (guard : d8085 p = 1) : d1802 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d8085, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35954 p hg
    simpa only [d8085, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38614 (p : Pattern) (guard : d8090 p = 1) : d1803 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38613 p hg
    simpa only [d8090, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35957 p hg
    simpa only [d8090, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38615 (p : Pattern) (guard : d8095 p = 1) : d1804 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38614 p hg
    simpa only [d8095, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38616 (p : Pattern) (guard : d8096 p = 1) : d1805 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38376 p hg
    simpa only [d8096, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38615 p hg
    simpa only [d8096, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38617 (p : Pattern) (guard : d8102 p = 1) : d1827 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38616 p hg
    simpa only [d8102, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38537 p hg
    simpa only [d8102, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38618 (p : Pattern) (guard : d8108 p = 1) : d1828 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38617 p hg
    simpa only [d8108, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38538 p hg
    simpa only [d8108, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38619 (p : Pattern) (guard : d8113 p = 1) : d1829 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38538 p hg
    simpa only [d8113, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38620 (p : Pattern) (guard : d8114 p = 1) : d1830 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38618 p hg
    simpa only [d8114, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38619 p hg
    simpa only [d8114, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38621 (p : Pattern) (guard : d8119 p = 1) : d1831 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38619 p hg
    simpa only [d8119, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38622 (p : Pattern) (guard : d8120 p = 1) : d1832 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38620 p hg
    simpa only [d8120, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38621 p hg
    simpa only [d8120, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38623 (p : Pattern) (guard : d8113 p = 1) : d1829 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38459 p hg
    simpa only [d8113, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38624 (p : Pattern) (guard : d8119 p = 1) : d1831 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38623 p hg
    simpa only [d8119, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38625 (p : Pattern) (guard : d8125 p = 1) : d1833 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38624 p hg
    simpa only [d8125, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38626 (p : Pattern) (guard : d8126 p = 1) : d1834 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38622 p hg
    simpa only [d8126, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38625 p hg
    simpa only [d8126, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38627 (p : Pattern) (guard : d8127 p = 1) : d1835 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38612 p hg
    simpa only [d8127, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38626 p hg
    simpa only [d8127, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38628 (p : Pattern) (guard : d8128 p = 1) : d1836 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38579 p hg
    simpa only [d8128, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38627 p hg
    simpa only [d8128, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38629 (p : Pattern) (guard : d8085 p = 1) : d1685 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d8085, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8085, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38630 (p : Pattern) (guard : d5843 p = 1) : d1683 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38631 (p : Pattern) (guard : d5847 p = 1) : d1684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38630 p hg
    simpa only [d5847, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38632 (p : Pattern) (guard : d8089 p = 1) : d1684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38633 (p : Pattern) (guard : d8090 p = 1) : d1686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38629 p hg
    simpa only [d8090, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38632 p hg
    simpa only [d8090, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38634 (p : Pattern) (guard : d8095 p = 1) : d1687 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38633 p hg
    simpa only [d8095, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38635 (p : Pattern) (guard : d8096 p = 1) : d1692 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38596 p hg
    simpa only [d8096, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38636 (p : Pattern) (guard : d8097 p = 1) : d1837 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38349 p hg
    simpa only [d8097, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38635 p hg
    simpa only [d8097, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38637 (p : Pattern) (guard : d8096 p = 1) : d1692 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d8096, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38638 (p : Pattern) (guard : d8089 p = 1) : d1695 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8089, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38361 p hg
    simpa only [d8089, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38639 (p : Pattern) (guard : d5854 p = 1) : d1694 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38361 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17101 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
