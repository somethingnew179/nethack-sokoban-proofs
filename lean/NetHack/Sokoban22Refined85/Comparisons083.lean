/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons082
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11620 (p : Pattern) (guard : d4967 p = 1) : d112 p ≤ (0 : Int) + d1888 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d112, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d112, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d112, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d112, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11621 (p : Pattern) (guard : d4967 p = 1) : d113 p ≤ (0 : Int) + d1889 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d113, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11618 p hg
    simpa only [d113, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d113, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11620 p hg
    simpa only [d113, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11622 (p : Pattern) (guard : d4967 p = 1) : d114 p ≤ (0 : Int) + d1890 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d114, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11619 p hg
    simpa only [d114, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d114, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11621 p hg
    simpa only [d114, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11623 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d1899 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11624 (p : Pattern) (guard : d4967 p = 1) : d118 p ≤ (0 : Int) + d1900 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d118, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d118, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d118, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11623 p hg
    simpa only [d4967, d118, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11625 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (0 : Int) + d1906 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11626 (p : Pattern) (guard : d4967 p = 1) : d122 p ≤ (0 : Int) + d1907 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d122, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d122, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d122, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11625 p hg
    simpa only [d4967, d122, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11627 (p : Pattern) (guard : d4967 p = 1) : d123 p ≤ (0 : Int) + d1908 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d123, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11624 p hg
    simpa only [d123, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d123, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11626 p hg
    simpa only [d123, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11628 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d1909 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d124, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11629 (p : Pattern) (guard : d4967 p = 1) : d125 p ≤ (0 : Int) + d1910 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d125, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d125, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d125, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d125, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11630 (p : Pattern) (guard : d4967 p = 1) : d126 p ≤ (0 : Int) + d1911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d126, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11628 p hg
    simpa only [d126, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d126, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d126, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11631 (p : Pattern) (guard : d4967 p = 1) : d127 p ≤ (0 : Int) + d1912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d127, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11627 p hg
    simpa only [d127, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d127, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11630 p hg
    simpa only [d127, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11632 (p : Pattern) (guard : d4967 p = 1) : d128 p ≤ (0 : Int) + d278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d128, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11517 p hg
    simpa only [d128, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d128, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d128, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11633 (p : Pattern) (guard : d4967 p = 1) : d129 p ≤ (0 : Int) + d1913 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d129, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11630 p hg
    simpa only [d129, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d129, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11632 p hg
    simpa only [d129, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11634 (p : Pattern) (guard : d4967 p = 1) : d130 p ≤ (0 : Int) + d1914 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d130, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11631 p hg
    simpa only [d130, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d130, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11633 p hg
    simpa only [d130, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11635 (p : Pattern) (guard : d4967 p = 1) : d131 p ≤ (0 : Int) + d1915 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d131, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11622 p hg
    simpa only [d131, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d131, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11634 p hg
    simpa only [d131, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11636 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d333 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11637 (p : Pattern) (guard : d4474 p = 1) : d103 p ≤ (0 : Int) + d1916 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11636 p hg
    simpa only [d4474, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11638 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1917 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d105, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11637 p hg
    simpa only [d4967, d105, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d105, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11608 p hg
    simpa only [d4967, d105, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11639 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11640 (p : Pattern) (guard : d4474 p = 1) : d116 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11641 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d1922 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11642 (p : Pattern) (guard : d4967 p = 1) : d132 p ≤ (0 : Int) + d1923 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d132, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d132, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d132, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11641 p hg
    simpa only [d4967, d132, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11643 (p : Pattern) (guard : d4967 p = 1) : d133 p ≤ (0 : Int) + d1924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d133, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11638 p hg
    simpa only [d133, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d133, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11642 p hg
    simpa only [d133, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11644 (p : Pattern) (guard : d4967 p = 1) : d134 p ≤ (0 : Int) + d1925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d134, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11617 p hg
    simpa only [d134, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d134, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d134, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11645 (p : Pattern) (guard : d4967 p = 1) : d135 p ≤ (0 : Int) + d1926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d135, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11643 p hg
    simpa only [d135, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d135, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11644 p hg
    simpa only [d135, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11646 (p : Pattern) (guard : d4967 p = 1) : d136 p ≤ (0 : Int) + d1927 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d136, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11617 p hg
    simpa only [d136, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d136, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d136, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11647 (p : Pattern) (guard : d4967 p = 1) : d137 p ≤ (0 : Int) + d1928 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d137, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11646 p hg
    simpa only [d137, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d137, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d137, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11648 (p : Pattern) (guard : d4967 p = 1) : d138 p ≤ (0 : Int) + d1929 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d138, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11645 p hg
    simpa only [d138, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d138, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11647 p hg
    simpa only [d138, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11649 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d1930 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d139, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d139, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d139, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d139, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11650 (p : Pattern) (guard : d4967 p = 1) : d140 p ≤ (0 : Int) + d1931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d140, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11626 p hg
    simpa only [d140, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d140, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11649 p hg
    simpa only [d140, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11651 (p : Pattern) (guard : d4967 p = 1) : d141 p ≤ (0 : Int) + d1932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d141, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d141, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d141, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11517 p hg
    simpa only [d141, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11652 (p : Pattern) (guard : d4967 p = 1) : d142 p ≤ (0 : Int) + d1933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d142, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11650 p hg
    simpa only [d142, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d142, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11651 p hg
    simpa only [d142, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11653 (p : Pattern) (guard : d4967 p = 1) : d143 p ≤ (0 : Int) + d1934 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d143, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d143, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d143, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d143, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11654 (p : Pattern) (guard : d4967 p = 1) : d144 p ≤ (0 : Int) + d1935 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d144, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11653 p hg
    simpa only [d144, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d144, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d144, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11655 (p : Pattern) (guard : d4967 p = 1) : d145 p ≤ (0 : Int) + d1936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d145, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11652 p hg
    simpa only [d145, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d145, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11654 p hg
    simpa only [d145, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11656 (p : Pattern) (guard : d4967 p = 1) : d146 p ≤ (0 : Int) + d1937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d146, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11648 p hg
    simpa only [d146, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d146, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11655 p hg
    simpa only [d146, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11657 (p : Pattern) (guard : d4967 p = 1) : d147 p ≤ (0 : Int) + d1938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d147, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11635 p hg
    simpa only [d147, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d147, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11656 p hg
    simpa only [d147, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11658 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d1943 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11659 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1944 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d105, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d105, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d105, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11658 p hg
    simpa only [d4967, d105, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11660 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d1952 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11661 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1953 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11660 p hg
    simpa only [d4967, d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11662 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11659 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11661 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11663 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d1958 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11664 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1959 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d105, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d105, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d105, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11663 p hg
    simpa only [d4967, d105, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11665 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (0 : Int) + d1967 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11666 (p : Pattern) (guard : d4967 p = 1) : d109 p ≤ (0 : Int) + d1968 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d109, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d109, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d109, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11665 p hg
    simpa only [d4967, d109, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11667 (p : Pattern) (guard : d4967 p = 1) : d110 p ≤ (0 : Int) + d1969 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d110, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11664 p hg
    simpa only [d110, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d110, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d110, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11668 (p : Pattern) (guard : d4967 p = 1) : d111 p ≤ (0 : Int) + d1970 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d111, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11662 p hg
    simpa only [d111, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d111, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11667 p hg
    simpa only [d111, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11669 (p : Pattern) (guard : d4967 p = 1) : d113 p ≤ (0 : Int) + d1971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d113, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11667 p hg
    simpa only [d113, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d113, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11620 p hg
    simpa only [d113, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11670 (p : Pattern) (guard : d4967 p = 1) : d114 p ≤ (0 : Int) + d1972 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d114, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11668 p hg
    simpa only [d114, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d114, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11669 p hg
    simpa only [d114, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11671 (p : Pattern) (guard : d4967 p = 1) : d132 p ≤ (0 : Int) + d1973 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d132, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d132, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d132, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11623 p hg
    simpa only [d4967, d132, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11672 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11673 (p : Pattern) (guard : d4474 p = 1) : d120 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11674 (p : Pattern) (guard : d4967 p = 1) : d148 p ≤ (0 : Int) + d1974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d148, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11673 p hg
    simpa only [d4967, d148, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d148, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11625 p hg
    simpa only [d4967, d148, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11675 (p : Pattern) (guard : d4967 p = 1) : d149 p ≤ (0 : Int) + d1975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d149, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d149, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d149, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11674 p hg
    simpa only [d149, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11676 (p : Pattern) (guard : d4967 p = 1) : d150 p ≤ (0 : Int) + d1976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d150, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11675 p hg
    simpa only [d150, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d150, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d150, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11677 (p : Pattern) (guard : d4967 p = 1) : d151 p ≤ (0 : Int) + d1977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d151, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11676 p hg
    simpa only [d151, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d151, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d151, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11678 (p : Pattern) (guard : d4967 p = 1) : d152 p ≤ (0 : Int) + d1978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d152, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11670 p hg
    simpa only [d152, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d152, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11677 p hg
    simpa only [d152, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11679 (p : Pattern) (guard : d4967 p = 1) : d133 p ≤ (0 : Int) + d1979 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d133, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11661 p hg
    simpa only [d133, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d133, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d133, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11680 (p : Pattern) (guard : d4967 p = 1) : d134 p ≤ (0 : Int) + d1980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d134, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d134, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d134, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d134, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11681 (p : Pattern) (guard : d4967 p = 1) : d135 p ≤ (0 : Int) + d1981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d135, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11679 p hg
    simpa only [d135, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d135, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11680 p hg
    simpa only [d135, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11682 (p : Pattern) (guard : d4967 p = 1) : d136 p ≤ (0 : Int) + d1982 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d136, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d136, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d136, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d136, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11683 (p : Pattern) (guard : d4967 p = 1) : d137 p ≤ (0 : Int) + d1983 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d137, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11682 p hg
    simpa only [d137, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d137, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d137, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11684 (p : Pattern) (guard : d4967 p = 1) : d138 p ≤ (0 : Int) + d1984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d138, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11681 p hg
    simpa only [d138, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d138, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11683 p hg
    simpa only [d138, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11685 (p : Pattern) (guard : d4967 p = 1) : d153 p ≤ (0 : Int) + d1985 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d153, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11674 p hg
    simpa only [d153, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d153, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d153, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11686 (p : Pattern) (guard : d4967 p = 1) : d154 p ≤ (0 : Int) + d1986 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d154, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11685 p hg
    simpa only [d154, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d154, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d154, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11687 (p : Pattern) (guard : d4967 p = 1) : d155 p ≤ (0 : Int) + d1987 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d155, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11686 p hg
    simpa only [d155, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d155, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d155, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11688 (p : Pattern) (guard : d4967 p = 1) : d156 p ≤ (0 : Int) + d1988 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d156, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11684 p hg
    simpa only [d156, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d156, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11687 p hg
    simpa only [d156, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11689 (p : Pattern) (guard : d4967 p = 1) : d157 p ≤ (0 : Int) + d1989 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d157, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11678 p hg
    simpa only [d157, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d157, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11688 p hg
    simpa only [d157, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11690 (p : Pattern) (guard : d4967 p = 1) : d158 p ≤ (0 : Int) + d1990 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d158, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11657 p hg
    simpa only [d158, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d158, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11689 p hg
    simpa only [d158, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11691 (p : Pattern) (guard : d4967 p = 1) : d159 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d159, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11620 p hg
    simpa only [d159, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d159, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d159, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11692 (p : Pattern) (guard : d4967 p = 1) : d160 p ≤ (0 : Int) + d1992 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d160, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11691 p hg
    simpa only [d160, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d160, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d160, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11693 (p : Pattern) (guard : d4967 p = 1) : d161 p ≤ (0 : Int) + d1993 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d161, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11692 p hg
    simpa only [d161, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d161, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d161, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11694 (p : Pattern) (guard : d4967 p = 1) : d162 p ≤ (0 : Int) + d1994 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d162, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11693 p hg
    simpa only [d162, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d162, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d162, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11695 (p : Pattern) (guard : d4967 p = 1) : d163 p ≤ (0 : Int) + d1995 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d163, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11689 p hg
    simpa only [d163, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d163, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11694 p hg
    simpa only [d163, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11696 (p : Pattern) (guard : d4967 p = 1) : d164 p ≤ (0 : Int) + d1996 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d164, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11690 p hg
    simpa only [d164, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d164, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11695 p hg
    simpa only [d164, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11697 (p : Pattern) (guard : d4967 p = 1) : d111 p ≤ (0 : Int) + d1997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d111, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11612 p hg
    simpa only [d111, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d111, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11618 p hg
    simpa only [d111, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11698 (p : Pattern) (guard : d4967 p = 1) : d114 p ≤ (0 : Int) + d1998 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d114, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11697 p hg
    simpa only [d114, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d114, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11621 p hg
    simpa only [d114, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11699 (p : Pattern) (guard : d4967 p = 1) : d131 p ≤ (0 : Int) + d1999 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d131, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11698 p hg
    simpa only [d131, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d131, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11634 p hg
    simpa only [d131, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11700 (p : Pattern) (guard : d4967 p = 1) : d133 p ≤ (0 : Int) + d2000 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d133, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11612 p hg
    simpa only [d133, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d133, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11642 p hg
    simpa only [d133, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11701 (p : Pattern) (guard : d4967 p = 1) : d135 p ≤ (0 : Int) + d2001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d135, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11700 p hg
    simpa only [d135, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d135, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11644 p hg
    simpa only [d135, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11702 (p : Pattern) (guard : d4967 p = 1) : d138 p ≤ (0 : Int) + d2002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d138, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11701 p hg
    simpa only [d138, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d138, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11647 p hg
    simpa only [d138, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11703 (p : Pattern) (guard : d4967 p = 1) : d146 p ≤ (0 : Int) + d2003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d146, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11702 p hg
    simpa only [d146, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d146, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11655 p hg
    simpa only [d146, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11704 (p : Pattern) (guard : d4967 p = 1) : d147 p ≤ (0 : Int) + d2004 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d147, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11699 p hg
    simpa only [d147, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d147, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11703 p hg
    simpa only [d147, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11705 (p : Pattern) (guard : d4967 p = 1) : d158 p ≤ (0 : Int) + d2005 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d158, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11704 p hg
    simpa only [d158, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d158, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11689 p hg
    simpa only [d158, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11706 (p : Pattern) (guard : d4967 p = 1) : d165 p ≤ (0 : Int) + d2006 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d165, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11689 p hg
    simpa only [d165, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d165, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d165, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11707 (p : Pattern) (guard : d4967 p = 1) : d166 p ≤ (0 : Int) + d2007 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d166, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11705 p hg
    simpa only [d166, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d166, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11706 p hg
    simpa only [d166, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11708 (p : Pattern) (guard : d4967 p = 1) : d167 p ≤ (0 : Int) + d2008 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d167, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11696 p hg
    simpa only [d167, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d167, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11707 p hg
    simpa only [d167, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11709 (p : Pattern) (guard : d4967 p = 1) : d168 p ≤ (0 : Int) + d2009 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d168, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11583 p hg
    simpa only [d168, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d168, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11708 p hg
    simpa only [d168, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11710 (p : Pattern) (guard : d4967 p = 1) : d169 p ≤ (0 : Int) + d2010 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d169, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11605 p hg
    simpa only [d169, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d169, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11709 p hg
    simpa only [d169, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11711 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d2013 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11712 (p : Pattern) (guard : d4967 p = 1) : d20 p ≤ (0 : Int) + d2014 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d20, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d4967, d20, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d20, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11711 p hg
    simpa only [d4967, d20, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11713 (p : Pattern) (guard : d4967 p = 1) : d21 p ≤ (0 : Int) + d2015 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d21, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11526 p hg
    simpa only [d21, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d21, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11712 p hg
    simpa only [d21, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11714 (p : Pattern) (guard : d4967 p = 1) : d22 p ≤ (0 : Int) + d2016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d22, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11526 p hg
    simpa only [d22, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d22, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11713 p hg
    simpa only [d22, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11715 (p : Pattern) (guard : d4967 p = 1) : d28 p ≤ (0 : Int) + d2017 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d28, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11713 p hg
    simpa only [d28, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d28, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11538 p hg
    simpa only [d28, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11716 (p : Pattern) (guard : d4967 p = 1) : d29 p ≤ (0 : Int) + d2018 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d29, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11714 p hg
    simpa only [d29, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d29, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11715 p hg
    simpa only [d29, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11717 (p : Pattern) (guard : d4967 p = 1) : d170 p ≤ (0 : Int) + d2019 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d170, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d170, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d170, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11477 p hg
    simpa only [d4967, d170, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11718 (p : Pattern) (guard : d4967 p = 1) : d171 p ≤ (0 : Int) + d2020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d171, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11541 p hg
    simpa only [d171, d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d171, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11717 p hg
    simpa only [d171, d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11719 (p : Pattern) (guard : d4967 p = 1) : d172 p ≤ (0 : Int) + d2021 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d172, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d172, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d172, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d4967, d172, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11720 (p : Pattern) (guard : d4967 p = 1) : d173 p ≤ (0 : Int) + d2022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d173, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11543 p hg
    simpa only [d4967, d173, d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d173, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d173, d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11721 (p : Pattern) (guard : d4967 p = 1) : d174 p ≤ (0 : Int) + d2023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d174, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11719 p hg
    simpa only [d174, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d174, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d174, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11722 (p : Pattern) (guard : d4967 p = 1) : d175 p ≤ (0 : Int) + d2024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d175, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11718 p hg
    simpa only [d175, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d175, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11721 p hg
    simpa only [d175, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11723 (p : Pattern) (guard : d4967 p = 1) : d176 p ≤ (0 : Int) + d2025 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d176, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d176, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d176, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d176, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11724 (p : Pattern) (guard : d4967 p = 1) : d177 p ≤ (0 : Int) + d2026 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d177, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11723 p hg
    simpa only [d177, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d177, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11520 p hg
    simpa only [d177, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11725 (p : Pattern) (guard : d4967 p = 1) : d178 p ≤ (0 : Int) + d2027 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d178, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11722 p hg
    simpa only [d178, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d178, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11724 p hg
    simpa only [d178, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11726 (p : Pattern) (guard : d4967 p = 1) : d179 p ≤ (0 : Int) + d2028 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d179, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11716 p hg
    simpa only [d179, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d179, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11725 p hg
    simpa only [d179, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11727 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d2031 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11728 (p : Pattern) (guard : d4967 p = 1) : d53 p ≤ (0 : Int) + d2032 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d53, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d53, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d53, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11727 p hg
    simpa only [d4967, d53, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11729 (p : Pattern) (guard : d4967 p = 1) : d54 p ≤ (0 : Int) + d2033 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d54, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11526 p hg
    simpa only [d54, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d54, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11728 p hg
    simpa only [d54, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11730 (p : Pattern) (guard : d4967 p = 1) : d55 p ≤ (0 : Int) + d2034 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d55, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11712 p hg
    simpa only [d55, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d55, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d55, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11731 (p : Pattern) (guard : d4967 p = 1) : d56 p ≤ (0 : Int) + d2035 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d56, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11729 p hg
    simpa only [d56, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d56, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11730 p hg
    simpa only [d56, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11732 (p : Pattern) (guard : d4967 p = 1) : d61 p ≤ (0 : Int) + d2036 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d61, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11712 p hg
    simpa only [d61, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d61, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d61, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11733 (p : Pattern) (guard : d4967 p = 1) : d64 p ≤ (0 : Int) + d2037 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d64, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11732 p hg
    simpa only [d64, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d64, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d64, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11734 (p : Pattern) (guard : d4967 p = 1) : d65 p ≤ (0 : Int) + d2038 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d65, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11731 p hg
    simpa only [d65, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d65, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11733 p hg
    simpa only [d65, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11735 (p : Pattern) (guard : d4967 p = 1) : d180 p ≤ (0 : Int) + d2039 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d180, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11717 p hg
    simpa only [d180, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d180, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d180, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11736 (p : Pattern) (guard : d4967 p = 1) : d181 p ≤ (0 : Int) + d2040 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d181, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d181, d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d181, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d181, d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11737 (p : Pattern) (guard : d4967 p = 1) : d182 p ≤ (0 : Int) + d2041 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d182, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11735 p hg
    simpa only [d182, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d182, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11736 p hg
    simpa only [d182, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11738 (p : Pattern) (guard : d4967 p = 1) : d183 p ≤ (0 : Int) + d2042 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d183, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d183, d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d183, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d183, d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11739 (p : Pattern) (guard : d4967 p = 1) : d184 p ≤ (0 : Int) + d2043 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d184, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11738 p hg
    simpa only [d184, d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d184, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d184, d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11740 (p : Pattern) (guard : d4967 p = 1) : d185 p ≤ (0 : Int) + d2044 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d185, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11737 p hg
    simpa only [d185, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d185, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11739 p hg
    simpa only [d185, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11741 (p : Pattern) (guard : d4967 p = 1) : d186 p ≤ (0 : Int) + d2045 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d186, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11734 p hg
    simpa only [d186, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d186, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11740 p hg
    simpa only [d186, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11742 (p : Pattern) (guard : d4967 p = 1) : d187 p ≤ (0 : Int) + d2046 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d187, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11726 p hg
    simpa only [d187, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d187, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11741 p hg
    simpa only [d187, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11743 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d2049 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11744 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d2050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d16, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11743 p hg
    simpa only [d4967, d16, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11745 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d2055 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11746 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d2056 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d16, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11745 p hg
    simpa only [d4967, d16, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11747 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d2057 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11744 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11746 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11748 (p : Pattern) (guard : d4967 p = 1) : d188 p ≤ (0 : Int) + d2058 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d188, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11747 p hg
    simpa only [d188, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d188, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11545 p hg
    simpa only [d188, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11749 (p : Pattern) (guard : d4967 p = 1) : d189 p ≤ (0 : Int) + d2059 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d189, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11748 p hg
    simpa only [d189, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d189, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11546 p hg
    simpa only [d189, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11750 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11751 (p : Pattern) (guard : d4474 p = 1) : d191 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11750 p hg
    simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11752 (p : Pattern) (guard : d0 p = 1) : d192 p ≤ (0 : Int) + d2062 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11753 (p : Pattern) (guard : d4967 p = 1) : d193 p ≤ (0 : Int) + d2063 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d193, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11751 p hg
    simpa only [d4967, d193, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d193, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11752 p hg
    simpa only [d4967, d193, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11754 (p : Pattern) (guard : d4967 p = 1) : d194 p ≤ (0 : Int) + d2064 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d194, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d194, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d194, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11753 p hg
    simpa only [d194, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11755 (p : Pattern) (guard : d4967 p = 1) : d195 p ≤ (0 : Int) + d2065 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d195, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11754 p hg
    simpa only [d195, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d195, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d195, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11756 (p : Pattern) (guard : d4967 p = 1) : d196 p ≤ (0 : Int) + d2066 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d196, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11755 p hg
    simpa only [d196, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d196, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d196, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11757 (p : Pattern) (guard : d4967 p = 1) : d197 p ≤ (0 : Int) + d2067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d197, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11749 p hg
    simpa only [d197, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d197, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11756 p hg
    simpa only [d197, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11758 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d2072 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11759 (p : Pattern) (guard : d4967 p = 1) : d53 p ≤ (0 : Int) + d2073 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d53, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d53, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d53, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11758 p hg
    simpa only [d4967, d53, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
