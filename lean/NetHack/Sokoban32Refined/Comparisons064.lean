/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8960 (p : Pattern) (guard : d1690 p = 1) : d49 p ≤ (2 : Int) + d1866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8952 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8936 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8961 (p : Pattern) (guard : d1690 p = 1) : d50 p ≤ (2 : Int) + d1874 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d50, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8959 p hg
    simpa only [d50, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d50, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8960 p hg
    simpa only [d50, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8962 (p : Pattern) (guard : d1690 p = 1) : d51 p ≤ (2 : Int) + d1875 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d51, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8958 p hg
    simpa only [d51, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d51, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8961 p hg
    simpa only [d51, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8963 (p : Pattern) (guard : d1690 p = 1) : d52 p ≤ (2 : Int) + d1876 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d52, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d52, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d52, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d52, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8964 (p : Pattern) (guard : d1690 p = 1) : d53 p ≤ (2 : Int) + d1877 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d53, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8922 p hg
    simpa only [d53, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d53, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8963 p hg
    simpa only [d53, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8965 (p : Pattern) (guard : d1690 p = 1) : d54 p ≤ (2 : Int) + d1878 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d54, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8929 p hg
    simpa only [d54, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d54, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d54, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8966 (p : Pattern) (guard : d1690 p = 1) : d55 p ≤ (2 : Int) + d1879 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d55, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8936 p hg
    simpa only [d55, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d55, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8965 p hg
    simpa only [d55, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8967 (p : Pattern) (guard : d1690 p = 1) : d56 p ≤ (2 : Int) + d1880 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d56, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8964 p hg
    simpa only [d56, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d56, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8966 p hg
    simpa only [d56, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8968 (p : Pattern) (guard : d1690 p = 1) : d57 p ≤ (2 : Int) + d1881 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d57, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8964 p hg
    simpa only [d57, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d57, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8967 p hg
    simpa only [d57, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8969 (p : Pattern) (guard : d1690 p = 1) : d58 p ≤ (2 : Int) + d1878 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d58, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d58, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d58, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d58, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8970 (p : Pattern) (guard : d1690 p = 1) : d59 p ≤ (2 : Int) + d1879 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d59, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8945 p hg
    simpa only [d59, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d59, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8969 p hg
    simpa only [d59, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8971 (p : Pattern) (guard : d1690 p = 1) : d60 p ≤ (2 : Int) + d1880 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d60, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8964 p hg
    simpa only [d60, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d60, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8970 p hg
    simpa only [d60, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8972 (p : Pattern) (guard : d1690 p = 1) : d61 p ≤ (2 : Int) + d1878 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d61, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8949 p hg
    simpa only [d61, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d61, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d61, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8973 (p : Pattern) (guard : d1690 p = 1) : d62 p ≤ (2 : Int) + d1879 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d62, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8952 p hg
    simpa only [d62, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d62, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8972 p hg
    simpa only [d62, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8974 (p : Pattern) (guard : d1690 p = 1) : d63 p ≤ (2 : Int) + d1879 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8973 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8966 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8975 (p : Pattern) (guard : d1690 p = 1) : d64 p ≤ (2 : Int) + d1882 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d64, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8971 p hg
    simpa only [d64, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d64, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8974 p hg
    simpa only [d64, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8976 (p : Pattern) (guard : d1690 p = 1) : d65 p ≤ (2 : Int) + d1883 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d65, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8968 p hg
    simpa only [d65, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d65, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d65, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8977 (p : Pattern) (guard : d1690 p = 1) : d66 p ≤ (2 : Int) + d1884 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d66, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8962 p hg
    simpa only [d66, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d66, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8976 p hg
    simpa only [d66, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8978 (p : Pattern) (guard : d1690 p = 1) : d67 p ≤ (2 : Int) + d1885 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d67, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8956 p hg
    simpa only [d67, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d67, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8977 p hg
    simpa only [d67, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8979 (p : Pattern) (guard : d1690 p = 1) : d68 p ≤ (2 : Int) + d1886 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d68, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8951 p hg
    simpa only [d68, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d68, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d68, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8980 (p : Pattern) (guard : d1690 p = 1) : d69 p ≤ (2 : Int) + d1887 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d69, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8951 p hg
    simpa only [d69, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d69, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8979 p hg
    simpa only [d69, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8981 (p : Pattern) (guard : d1690 p = 1) : d70 p ≤ (2 : Int) + d1886 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d70, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8935 p hg
    simpa only [d70, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d70, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d70, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8982 (p : Pattern) (guard : d1690 p = 1) : d71 p ≤ (2 : Int) + d1887 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d71, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8935 p hg
    simpa only [d71, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d71, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8981 p hg
    simpa only [d71, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8983 (p : Pattern) (guard : d1690 p = 1) : d72 p ≤ (2 : Int) + d1887 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8980 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8982 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8984 (p : Pattern) (guard : d1690 p = 1) : d73 p ≤ (2 : Int) + d1888 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d73, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8938 p hg
    simpa only [d73, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d73, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8983 p hg
    simpa only [d73, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8985 (p : Pattern) (guard : d1690 p = 1) : d74 p ≤ (2 : Int) + d1889 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d74, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8939 p hg
    simpa only [d74, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d74, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8984 p hg
    simpa only [d74, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8986 (p : Pattern) (guard : d1690 p = 1) : d75 p ≤ (2 : Int) + d1886 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8979 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8981 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8987 (p : Pattern) (guard : d1690 p = 1) : d76 p ≤ (2 : Int) + d1890 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d76, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8938 p hg
    simpa only [d76, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d76, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8986 p hg
    simpa only [d76, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8988 (p : Pattern) (guard : d1690 p = 1) : d77 p ≤ (2 : Int) + d1891 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d77, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8939 p hg
    simpa only [d77, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d77, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8987 p hg
    simpa only [d77, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8989 (p : Pattern) (guard : d1690 p = 1) : d78 p ≤ (2 : Int) + d1892 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d78, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8985 p hg
    simpa only [d78, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d78, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8988 p hg
    simpa only [d78, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8990 (p : Pattern) (guard : d1690 p = 1) : d79 p ≤ (2 : Int) + d1893 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d79, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8957 p hg
    simpa only [d79, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d79, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8986 p hg
    simpa only [d79, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8991 (p : Pattern) (guard : d1690 p = 1) : d80 p ≤ (2 : Int) + d1894 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d80, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8958 p hg
    simpa only [d80, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d80, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8990 p hg
    simpa only [d80, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8992 (p : Pattern) (guard : d1690 p = 1) : d81 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d81, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8967 p hg
    simpa only [d81, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d81, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8986 p hg
    simpa only [d81, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8993 (p : Pattern) (guard : d1690 p = 1) : d82 p ≤ (2 : Int) + d1896 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d82, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8968 p hg
    simpa only [d82, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d82, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8992 p hg
    simpa only [d82, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8994 (p : Pattern) (guard : d1690 p = 1) : d83 p ≤ (2 : Int) + d1897 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d83, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8991 p hg
    simpa only [d83, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d83, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8993 p hg
    simpa only [d83, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8995 (p : Pattern) (guard : d1690 p = 1) : d84 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d84, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8989 p hg
    simpa only [d84, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d84, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8994 p hg
    simpa only [d84, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8996 (p : Pattern) (guard : d1690 p = 1) : d85 p ≤ (2 : Int) + d1899 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d85, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d85, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d85, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8995 p hg
    simpa only [d85, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8997 (p : Pattern) (guard : d1690 p = 1) : d86 p ≤ (2 : Int) + d1900 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d86, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d86, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d86, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8963 p hg
    simpa only [d86, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8998 (p : Pattern) (guard : d1690 p = 1) : d87 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d87, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8929 p hg
    simpa only [d87, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d87, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8965 p hg
    simpa only [d87, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8999 (p : Pattern) (guard : d1690 p = 1) : d88 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d88, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8997 p hg
    simpa only [d88, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d88, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8998 p hg
    simpa only [d88, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9000 (p : Pattern) (guard : d1690 p = 1) : d89 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d89, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8997 p hg
    simpa only [d89, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d89, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8999 p hg
    simpa only [d89, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9001 (p : Pattern) (guard : d1690 p = 1) : d90 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d90, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d90, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d90, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8969 p hg
    simpa only [d90, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9002 (p : Pattern) (guard : d1690 p = 1) : d91 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d91, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8997 p hg
    simpa only [d91, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d91, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9001 p hg
    simpa only [d91, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9003 (p : Pattern) (guard : d1690 p = 1) : d92 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d92, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8949 p hg
    simpa only [d92, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d92, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8972 p hg
    simpa only [d92, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9004 (p : Pattern) (guard : d1690 p = 1) : d93 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9003 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8998 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9005 (p : Pattern) (guard : d1690 p = 1) : d94 p ≤ (2 : Int) + d1904 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d94, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9002 p hg
    simpa only [d94, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d94, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9004 p hg
    simpa only [d94, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9006 (p : Pattern) (guard : d1690 p = 1) : d95 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d95, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9000 p hg
    simpa only [d95, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d95, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9005 p hg
    simpa only [d95, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9007 (p : Pattern) (guard : d1690 p = 1) : d96 p ≤ (2 : Int) + d1906 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d96, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8956 p hg
    simpa only [d96, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d96, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9006 p hg
    simpa only [d96, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9008 (p : Pattern) (guard : d1690 p = 1) : d97 p ≤ (2 : Int) + d1907 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d97, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8921 p hg
    simpa only [d97, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d97, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d97, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9009 (p : Pattern) (guard : d1690 p = 1) : d98 p ≤ (2 : Int) + d1908 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d98, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8921 p hg
    simpa only [d98, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d98, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9008 p hg
    simpa only [d98, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9010 (p : Pattern) (guard : d1690 p = 1) : d99 p ≤ (2 : Int) + d1909 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d99, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9009 p hg
    simpa only [d99, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d99, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8982 p hg
    simpa only [d99, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9011 (p : Pattern) (guard : d1690 p = 1) : d100 p ≤ (2 : Int) + d1910 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d100, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9009 p hg
    simpa only [d100, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d100, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9010 p hg
    simpa only [d100, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9012 (p : Pattern) (guard : d1690 p = 1) : d101 p ≤ (2 : Int) + d1911 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d101, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9010 p hg
    simpa only [d101, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d101, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8983 p hg
    simpa only [d101, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9013 (p : Pattern) (guard : d1690 p = 1) : d102 p ≤ (2 : Int) + d1912 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d102, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9011 p hg
    simpa only [d102, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d102, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9012 p hg
    simpa only [d102, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9014 (p : Pattern) (guard : d1690 p = 1) : d103 p ≤ (2 : Int) + d1913 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d103, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9007 p hg
    simpa only [d103, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d103, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9013 p hg
    simpa only [d103, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9015 (p : Pattern) (guard : d1690 p = 1) : d104 p ≤ (2 : Int) + d1914 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d104, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8999 p hg
    simpa only [d104, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d104, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8986 p hg
    simpa only [d104, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9016 (p : Pattern) (guard : d1690 p = 1) : d105 p ≤ (2 : Int) + d1915 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d105, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9000 p hg
    simpa only [d105, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d105, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9015 p hg
    simpa only [d105, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9017 (p : Pattern) (guard : d1690 p = 1) : d106 p ≤ (2 : Int) + d1916 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d106, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8988 p hg
    simpa only [d106, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d106, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9016 p hg
    simpa only [d106, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9018 (p : Pattern) (guard : d1690 p = 1) : d107 p ≤ (2 : Int) + d1917 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d107, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9010 p hg
    simpa only [d107, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d107, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d107, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9019 (p : Pattern) (guard : d1690 p = 1) : d108 p ≤ (2 : Int) + d1918 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d108, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9011 p hg
    simpa only [d108, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d108, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9018 p hg
    simpa only [d108, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9020 (p : Pattern) (guard : d1690 p = 1) : d109 p ≤ (2 : Int) + d1919 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d109, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9008 p hg
    simpa only [d109, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d109, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8981 p hg
    simpa only [d109, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9021 (p : Pattern) (guard : d1690 p = 1) : d110 p ≤ (2 : Int) + d1920 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d110, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9008 p hg
    simpa only [d110, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d110, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9020 p hg
    simpa only [d110, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9022 (p : Pattern) (guard : d1690 p = 1) : d111 p ≤ (2 : Int) + d1921 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d111, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9020 p hg
    simpa only [d111, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d111, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d111, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9023 (p : Pattern) (guard : d1690 p = 1) : d112 p ≤ (2 : Int) + d1922 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d112, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9021 p hg
    simpa only [d112, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d112, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9022 p hg
    simpa only [d112, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9024 (p : Pattern) (guard : d1690 p = 1) : d113 p ≤ (2 : Int) + d1923 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d113, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9019 p hg
    simpa only [d113, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d113, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9023 p hg
    simpa only [d113, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9025 (p : Pattern) (guard : d1690 p = 1) : d114 p ≤ (2 : Int) + d1924 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d114, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9017 p hg
    simpa only [d114, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d114, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9024 p hg
    simpa only [d114, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9026 (p : Pattern) (guard : d1690 p = 1) : d115 p ≤ (2 : Int) + d1925 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d115, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9014 p hg
    simpa only [d115, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d115, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9025 p hg
    simpa only [d115, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9027 (p : Pattern) (guard : d1690 p = 1) : d116 p ≤ (2 : Int) + d1926 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d116, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8996 p hg
    simpa only [d116, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d116, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9026 p hg
    simpa only [d116, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9028 (p : Pattern) (guard : d1690 p = 1) : d117 p ≤ (2 : Int) + d1927 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d117, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8988 p hg
    simpa only [d117, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d117, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8994 p hg
    simpa only [d117, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9029 (p : Pattern) (guard : d1690 p = 1) : d118 p ≤ (2 : Int) + d1928 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d118, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d118, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d118, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9028 p hg
    simpa only [d118, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9030 (p : Pattern) (guard : d1690 p = 1) : d119 p ≤ (2 : Int) + d1864 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8929 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9031 (p : Pattern) (guard : d1690 p = 1) : d120 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d120, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9030 p hg
    simpa only [d120, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d120, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8969 p hg
    simpa only [d120, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9032 (p : Pattern) (guard : d1690 p = 1) : d121 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d121, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8997 p hg
    simpa only [d121, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d121, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9031 p hg
    simpa only [d121, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9033 (p : Pattern) (guard : d1690 p = 1) : d122 p ≤ (2 : Int) + d1904 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d122, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9032 p hg
    simpa only [d122, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d122, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9004 p hg
    simpa only [d122, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9034 (p : Pattern) (guard : d1690 p = 1) : d123 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d123, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9000 p hg
    simpa only [d123, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d123, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9033 p hg
    simpa only [d123, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9035 (p : Pattern) (guard : d1690 p = 1) : d124 p ≤ (2 : Int) + d1906 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d124, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8956 p hg
    simpa only [d124, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d124, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9034 p hg
    simpa only [d124, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9036 (p : Pattern) (guard : d1690 p = 1) : d125 p ≤ (2 : Int) + d1929 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d125, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9020 p hg
    simpa only [d125, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d125, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8986 p hg
    simpa only [d125, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9037 (p : Pattern) (guard : d1690 p = 1) : d126 p ≤ (2 : Int) + d1930 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d126, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9021 p hg
    simpa only [d126, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d126, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9036 p hg
    simpa only [d126, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9038 (p : Pattern) (guard : d1690 p = 1) : d127 p ≤ (2 : Int) + d1931 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d127, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9013 p hg
    simpa only [d127, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d127, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9037 p hg
    simpa only [d127, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9039 (p : Pattern) (guard : d1690 p = 1) : d128 p ≤ (2 : Int) + d1932 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d128, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9035 p hg
    simpa only [d128, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d128, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9038 p hg
    simpa only [d128, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9040 (p : Pattern) (guard : d1690 p = 1) : d129 p ≤ (2 : Int) + d1933 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d129, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8988 p hg
    simpa only [d129, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d129, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8993 p hg
    simpa only [d129, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9041 (p : Pattern) (guard : d1690 p = 1) : d130 p ≤ (2 : Int) + d1934 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d130, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9023 p hg
    simpa only [d130, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d130, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d130, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9042 (p : Pattern) (guard : d1690 p = 1) : d131 p ≤ (2 : Int) + d1935 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d131, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9040 p hg
    simpa only [d131, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d131, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9041 p hg
    simpa only [d131, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9043 (p : Pattern) (guard : d1690 p = 1) : d132 p ≤ (2 : Int) + d1936 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d132, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9039 p hg
    simpa only [d132, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d132, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9042 p hg
    simpa only [d132, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9044 (p : Pattern) (guard : d1690 p = 1) : d133 p ≤ (2 : Int) + d1937 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d133, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9029 p hg
    simpa only [d133, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d133, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9043 p hg
    simpa only [d133, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9045 (p : Pattern) (guard : d1690 p = 1) : d134 p ≤ (2 : Int) + d1938 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d134, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9027 p hg
    simpa only [d134, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d134, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9044 p hg
    simpa only [d134, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9046 (p : Pattern) (guard : d985 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare9047 (p : Pattern) (guard : d985 p = 1) : d4 p ≤ (2 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9046 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8723 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9048 (p : Pattern) (guard : d985 p = 1) : d5 p ≤ (2 : Int) + d5 p := by
  omega
theorem compare9049 (p : Pattern) (guard : d985 p = 1) : d6 p ≤ (2 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9047 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9048 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9050 (p : Pattern) (guard : d985 p = 1) : d7 p ≤ (2 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9047 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9051 (p : Pattern) (guard : d985 p = 1) : d8 p ≤ (2 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9049 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9050 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9052 (p : Pattern) (guard : d985 p = 1) : d1 p ≤ (2 : Int) + d1 p := by
  omega
theorem compare9053 (p : Pattern) (guard : d985 p = 1) : d10 p ≤ (2 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9052 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8734 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9054 (p : Pattern) (guard : d985 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  omega
theorem compare9055 (p : Pattern) (guard : d985 p = 1) : d12 p ≤ (2 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9053 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9054 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9056 (p : Pattern) (guard : d985 p = 1) : d13 p ≤ (2 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9053 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9057 (p : Pattern) (guard : d985 p = 1) : d14 p ≤ (2 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9055 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9056 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9058 (p : Pattern) (guard : d985 p = 1) : d15 p ≤ (2 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9051 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9057 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9059 (p : Pattern) (guard : d985 p = 1) : d16 p ≤ (2 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9051 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9058 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9060 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8723 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9061 (p : Pattern) (guard : d985 p = 1) : d18 p ≤ (2 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9047 p hg
    simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9060 p hg
    simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9062 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9060 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9063 (p : Pattern) (guard : d985 p = 1) : d20 p ≤ (2 : Int) + d986 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9061 p hg
    simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9062 p hg
    simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9064 (p : Pattern) (guard : d985 p = 1) : d21 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8734 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9065 (p : Pattern) (guard : d985 p = 1) : d22 p ≤ (2 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9053 p hg
    simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9064 p hg
    simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9066 (p : Pattern) (guard : d985 p = 1) : d23 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9064 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9067 (p : Pattern) (guard : d985 p = 1) : d24 p ≤ (2 : Int) + d987 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9065 p hg
    simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9066 p hg
    simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9068 (p : Pattern) (guard : d985 p = 1) : d25 p ≤ (2 : Int) + d988 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9063 p hg
    simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9067 p hg
    simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9069 (p : Pattern) (guard : d985 p = 1) : d26 p ≤ (2 : Int) + d989 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9063 p hg
    simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9068 p hg
    simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9070 (p : Pattern) (guard : d985 p = 1) : d27 p ≤ (2 : Int) + d990 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9059 p hg
    simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9069 p hg
    simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9071 (p : Pattern) (guard : d985 p = 1) : d28 p ≤ (2 : Int) + d991 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9059 p hg
    simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9070 p hg
    simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9072 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9073 (p : Pattern) (guard : d985 p = 1) : d29 p ≤ (2 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9072 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9074 (p : Pattern) (guard : d985 p = 1) : d30 p ≤ (2 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9073 p hg
    simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9075 (p : Pattern) (guard : d985 p = 1) : d31 p ≤ (2 : Int) + d992 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9047 p hg
    simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9074 p hg
    simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9076 (p : Pattern) (guard : d985 p = 1) : d32 p ≤ (2 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9074 p hg
    simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9077 (p : Pattern) (guard : d985 p = 1) : d33 p ≤ (2 : Int) + d993 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9075 p hg
    simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9076 p hg
    simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9078 (p : Pattern) (guard : d985 p = 1) : d34 p ≤ (2 : Int) + d994 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9077 p hg
    simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9067 p hg
    simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9079 (p : Pattern) (guard : d985 p = 1) : d35 p ≤ (2 : Int) + d995 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9077 p hg
    simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9078 p hg
    simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9080 (p : Pattern) (guard : d985 p = 1) : d36 p ≤ (2 : Int) + d996 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9059 p hg
    simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9079 p hg
    simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9081 (p : Pattern) (guard : d985 p = 1) : d37 p ≤ (2 : Int) + d37 p := by
  omega
theorem compare9082 (p : Pattern) (guard : d985 p = 1) : d38 p ≤ (2 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9049 p hg
    simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9081 p hg
    simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9083 (p : Pattern) (guard : d985 p = 1) : d39 p ≤ (2 : Int) + d39 p := by
  omega
theorem compare9084 (p : Pattern) (guard : d985 p = 1) : d40 p ≤ (2 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9055 p hg
    simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9083 p hg
    simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9085 (p : Pattern) (guard : d985 p = 1) : d41 p ≤ (2 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9082 p hg
    simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9084 p hg
    simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9086 (p : Pattern) (guard : d985 p = 1) : d42 p ≤ (2 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9082 p hg
    simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9085 p hg
    simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9087 (p : Pattern) (guard : d985 p = 1) : d43 p ≤ (2 : Int) + d990 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9086 p hg
    simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9069 p hg
    simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9088 (p : Pattern) (guard : d985 p = 1) : d44 p ≤ (2 : Int) + d997 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9080 p hg
    simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9087 p hg
    simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9089 (p : Pattern) (guard : d985 p = 1) : d45 p ≤ (2 : Int) + d998 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9071 p hg
    simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9088 p hg
    simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9090 (p : Pattern) (guard : d985 p = 1) : d46 p ≤ (2 : Int) + d999 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9058 p hg
    simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9068 p hg
    simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9091 (p : Pattern) (guard : d985 p = 1) : d47 p ≤ (2 : Int) + d1000 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9058 p hg
    simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9090 p hg
    simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9092 (p : Pattern) (guard : d985 p = 1) : d48 p ≤ (2 : Int) + d1001 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9058 p hg
    simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9078 p hg
    simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9093 (p : Pattern) (guard : d985 p = 1) : d49 p ≤ (2 : Int) + d999 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9085 p hg
    simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9068 p hg
    simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9094 (p : Pattern) (guard : d985 p = 1) : d50 p ≤ (2 : Int) + d1002 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9092 p hg
    simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9093 p hg
    simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9095 (p : Pattern) (guard : d985 p = 1) : d51 p ≤ (2 : Int) + d1003 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9091 p hg
    simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9094 p hg
    simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9096 (p : Pattern) (guard : d985 p = 1) : d52 p ≤ (2 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9051 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9097 (p : Pattern) (guard : d985 p = 1) : d53 p ≤ (2 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9058 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9096 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9098 (p : Pattern) (guard : d985 p = 1) : d54 p ≤ (2 : Int) + d1004 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9063 p hg
    simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9099 (p : Pattern) (guard : d985 p = 1) : d55 p ≤ (2 : Int) + d1005 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9068 p hg
    simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9098 p hg
    simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
