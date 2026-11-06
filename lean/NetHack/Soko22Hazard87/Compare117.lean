import NetHack.Soko22Hazard87.Compare116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29250 (p : Pattern) (guard : d258878 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258877 p = 1 := by simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29249 p hg
    simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258751 p = 1 := by simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29061 p hg
    simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29251 (p : Pattern) (guard : d258879 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258878 p = 1 := by simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29250 p hg
    simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258752 p = 1 := by simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29063 p hg
    simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29252 (p : Pattern) (guard : d258880 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258879 p = 1 := by simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29251 p hg
    simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29253 (p : Pattern) (guard : d258881 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258880 p = 1 := by simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29252 p hg
    simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29254 (p : Pattern) (guard : d258882 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258881 p = 1 := by simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29253 p hg
    simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29255 (p : Pattern) (guard : d258883 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258882 p = 1 := by simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258756 p = 1 := by simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29068 p hg
    simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29256 (p : Pattern) (guard : d258884 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258883 p = 1 := by simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29255 p hg
    simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29257 (p : Pattern) (guard : d258885 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258884 p = 1 := by simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29256 p hg
    simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29258 (p : Pattern) (guard : d258886 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258885 p = 1 := by simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29257 p hg
    simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29259 (p : Pattern) (guard : d258887 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258886 p = 1 := by simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29258 p hg
    simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258760 p = 1 := by simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29072 p hg
    simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29260 (p : Pattern) (guard : d258888 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258887 p = 1 := by simpa only [d258888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29259 p hg
    simpa only [d258888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29261 (p : Pattern) (guard : d258889 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258888 p = 1 := by simpa only [d258889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29260 p hg
    simpa only [d258889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258762 p = 1 := by simpa only [d258889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29074 p hg
    simpa only [d258889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29262 (p : Pattern) (guard : d258890 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258889 p = 1 := by simpa only [d258890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29261 p hg
    simpa only [d258890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29263 (p : Pattern) (guard : d258891 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258890 p = 1 := by simpa only [d258891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29262 p hg
    simpa only [d258891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29264 (p : Pattern) (guard : d258892 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258892, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258892, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258891 p = 1 := by simpa only [d258892, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29263 p hg
    simpa only [d258892, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29265 (p : Pattern) (guard : d258893 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258892 p = 1 := by simpa only [d258893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29264 p hg
    simpa only [d258893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29266 (p : Pattern) (guard : d258894 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258893 p = 1 := by simpa only [d258894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29265 p hg
    simpa only [d258894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29267 (p : Pattern) (guard : d258895 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258894 p = 1 := by simpa only [d258895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29266 p hg
    simpa only [d258895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29268 (p : Pattern) (guard : d258896 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d258895 p = 1 := by simpa only [d258896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29267 p hg
    simpa only [d258896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29269 (p : Pattern) (guard : d258897 p = 1) : d47865 p ≤ (-1 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d258896 p = 1 := by simpa only [d258897, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29268 p hg
    simpa only [d258897, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258897, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29083 p hg
    simpa only [d258897, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29270 (p : Pattern) (guard : d258898 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d258868 p = 1 := by simpa only [d258898, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d258898, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258897 p = 1 := by simpa only [d258898, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29269 p hg
    simpa only [d258898, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29271 (p : Pattern) (guard : d258899 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258898 p = 1 := by simpa only [d258899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29270 p hg
    simpa only [d258899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29272 (p : Pattern) (guard : d258900 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258899 p = 1 := by simpa only [d258900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29271 p hg
    simpa only [d258900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29273 (p : Pattern) (guard : d258901 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258900 p = 1 := by simpa only [d258901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29272 p hg
    simpa only [d258901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29274 (p : Pattern) (guard : d258902 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258901 p = 1 := by simpa only [d258902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29273 p hg
    simpa only [d258902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29275 (p : Pattern) (guard : d258903 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258902 p = 1 := by simpa only [d258903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29274 p hg
    simpa only [d258903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29276 (p : Pattern) (guard : d258904 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258903 p = 1 := by simpa only [d258904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29275 p hg
    simpa only [d258904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29277 (p : Pattern) (guard : d258905 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d258778 p = 1 := by simpa only [d258905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29091 p hg
    simpa only [d258905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258904 p = 1 := by simpa only [d258905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29276 p hg
    simpa only [d258905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29278 (p : Pattern) (guard : d258906 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258833 p = 1 := by simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29148 p hg
    simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29279 (p : Pattern) (guard : d258907 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258906 p = 1 := by simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29278 p hg
    simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29280 (p : Pattern) (guard : d258908 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258907 p = 1 := by simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29279 p hg
    simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29281 (p : Pattern) (guard : d258909 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258908 p = 1 := by simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29280 p hg
    simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29282 (p : Pattern) (guard : d258910 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258909 p = 1 := by simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29283 (p : Pattern) (guard : d258911 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258910 p = 1 := by simpa only [d258911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29282 p hg
    simpa only [d258911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29284 (p : Pattern) (guard : d258912 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258911 p = 1 := by simpa only [d258912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29283 p hg
    simpa only [d258912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29285 (p : Pattern) (guard : d258913 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258849 p = 1 := by simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29164 p hg
    simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29286 (p : Pattern) (guard : d258914 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258913 p = 1 := by simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29285 p hg
    simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29287 (p : Pattern) (guard : d258915 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258914 p = 1 := by simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29286 p hg
    simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29288 (p : Pattern) (guard : d258916 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258915 p = 1 := by simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29287 p hg
    simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29289 (p : Pattern) (guard : d258917 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258909 p = 1 := by simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258916 p = 1 := by simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29288 p hg
    simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29290 (p : Pattern) (guard : d258918 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258910 p = 1 := by simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29282 p hg
    simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258917 p = 1 := by simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29289 p hg
    simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29291 (p : Pattern) (guard : d258919 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258918 p = 1 := by simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29290 p hg
    simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29292 (p : Pattern) (guard : d258920 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258912 p = 1 := by simpa only [d258920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29284 p hg
    simpa only [d258920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258919 p = 1 := by simpa only [d258920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29291 p hg
    simpa only [d258920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29293 (p : Pattern) (guard : d258921 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258830 p = 1 := by simpa only [d258921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29145 p hg
    simpa only [d258921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29294 (p : Pattern) (guard : d258922 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258921 p = 1 := by simpa only [d258922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29293 p hg
    simpa only [d258922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29295 (p : Pattern) (guard : d258923 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258922 p = 1 := by simpa only [d258923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29294 p hg
    simpa only [d258923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258795 p = 1 := by simpa only [d258923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29108 p hg
    simpa only [d258923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29296 (p : Pattern) (guard : d258924 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258923 p = 1 := by simpa only [d258924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29295 p hg
    simpa only [d258924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29297 (p : Pattern) (guard : d258925 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258924 p = 1 := by simpa only [d258925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29296 p hg
    simpa only [d258925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29298 (p : Pattern) (guard : d258926 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258925 p = 1 := by simpa only [d258926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29297 p hg
    simpa only [d258926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29299 (p : Pattern) (guard : d258927 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258829 p = 1 := by simpa only [d258927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29144 p hg
    simpa only [d258927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29300 (p : Pattern) (guard : d258928 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258927 p = 1 := by simpa only [d258928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29299 p hg
    simpa only [d258928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29301 (p : Pattern) (guard : d258929 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258928 p = 1 := by simpa only [d258929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29300 p hg
    simpa only [d258929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29302 (p : Pattern) (guard : d258930 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258929 p = 1 := by simpa only [d258930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29301 p hg
    simpa only [d258930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258802 p = 1 := by simpa only [d258930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29115 p hg
    simpa only [d258930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29303 (p : Pattern) (guard : d258931 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258930 p = 1 := by simpa only [d258931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29302 p hg
    simpa only [d258931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29304 (p : Pattern) (guard : d258932 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258931 p = 1 := by simpa only [d258932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29303 p hg
    simpa only [d258932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29305 (p : Pattern) (guard : d1998 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29120 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29306 (p : Pattern) (guard : d258933 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29305 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29121 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29307 (p : Pattern) (guard : d258934 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29306 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29308 (p : Pattern) (guard : d258935 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29307 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29309 (p : Pattern) (guard : d258936 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29308 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29310 (p : Pattern) (guard : d258937 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29309 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29311 (p : Pattern) (guard : d258938 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29310 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29126 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29312 (p : Pattern) (guard : d258939 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29311 p hg
    simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29313 (p : Pattern) (guard : d258940 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29126 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29314 (p : Pattern) (guard : d258941 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29313 p hg
    simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29315 (p : Pattern) (guard : d258942 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29312 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29314 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29316 (p : Pattern) (guard : d258943 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29315 p hg
    simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29317 (p : Pattern) (guard : d258944 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258943 p = 1 := by simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29316 p hg
    simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29318 (p : Pattern) (guard : d258945 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258944 p = 1 := by simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29317 p hg
    simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29319 (p : Pattern) (guard : d258946 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258945 p = 1 := by simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29318 p hg
    simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29320 (p : Pattern) (guard : d258947 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258946 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29319 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258818 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29133 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29321 (p : Pattern) (guard : d258948 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29314 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28912 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29322 (p : Pattern) (guard : d258949 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29321 p hg
    simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29323 (p : Pattern) (guard : d258950 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258949 p = 1 := by simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29322 p hg
    simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29324 (p : Pattern) (guard : d258951 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258950 p = 1 := by simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29323 p hg
    simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29325 (p : Pattern) (guard : d258952 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258951 p = 1 := by simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29324 p hg
    simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29326 (p : Pattern) (guard : d258953 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258952 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28921 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29327 (p : Pattern) (guard : d258954 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258947 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29320 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258953 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29326 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29328 (p : Pattern) (guard : d258955 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258954 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29327 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258820 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29135 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29329 (p : Pattern) (guard : d258956 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258955 p = 1 := by simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29328 p hg
    simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29330 (p : Pattern) (guard : d258957 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258956 p = 1 := by simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29329 p hg
    simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29331 (p : Pattern) (guard : d258958 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258957 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29330 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258823 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29138 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29332 (p : Pattern) (guard : d258959 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258958 p = 1 := by simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29331 p hg
    simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258824 p = 1 := by simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29139 p hg
    simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29333 (p : Pattern) (guard : d258960 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258959 p = 1 := by simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29332 p hg
    simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29334 (p : Pattern) (guard : d258961 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258960 p = 1 := by simpa only [d258961, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29333 p hg
    simpa only [d258961, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258961, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d258961, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29335 (p : Pattern) (guard : d258962 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258962, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d258962, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258961 p = 1 := by simpa only [d258962, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29334 p hg
    simpa only [d258962, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29336 (p : Pattern) (guard : d258963 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258962 p = 1 := by simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29335 p hg
    simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258828 p = 1 := by simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29143 p hg
    simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29337 (p : Pattern) (guard : d258964 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258963 p = 1 := by simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29336 p hg
    simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29338 (p : Pattern) (guard : d258965 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258964 p = 1 := by simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29337 p hg
    simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29339 (p : Pattern) (guard : d258966 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258965 p = 1 := by simpa only [d258966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29338 p hg
    simpa only [d258966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29340 (p : Pattern) (guard : d258967 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258966 p = 1 := by simpa only [d258967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29339 p hg
    simpa only [d258967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258832 p = 1 := by simpa only [d258967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29147 p hg
    simpa only [d258967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29341 (p : Pattern) (guard : d258968 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258967 p = 1 := by simpa only [d258968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29340 p hg
    simpa only [d258968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29342 (p : Pattern) (guard : d258969 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258828 p = 1 := by simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29143 p hg
    simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29343 (p : Pattern) (guard : d258970 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258969 p = 1 := by simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29342 p hg
    simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29344 (p : Pattern) (guard : d258971 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258970 p = 1 := by simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29343 p hg
    simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29345 (p : Pattern) (guard : d258972 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258971 p = 1 := by simpa only [d258972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29344 p hg
    simpa only [d258972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29346 (p : Pattern) (guard : d258973 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258972 p = 1 := by simpa only [d258973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29345 p hg
    simpa only [d258973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29347 (p : Pattern) (guard : d258974 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258973 p = 1 := by simpa only [d258974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29346 p hg
    simpa only [d258974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29348 (p : Pattern) (guard : d258975 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258968 p = 1 := by simpa only [d258975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29341 p hg
    simpa only [d258975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258974 p = 1 := by simpa only [d258975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29347 p hg
    simpa only [d258975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29349 (p : Pattern) (guard : d258976 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d258932 p = 1 := by simpa only [d258976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29304 p hg
    simpa only [d258976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258975 p = 1 := by simpa only [d258976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29348 p hg
    simpa only [d258976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29350 (p : Pattern) (guard : d258977 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d258926 p = 1 := by simpa only [d258977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29298 p hg
    simpa only [d258977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258976 p = 1 := by simpa only [d258977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29349 p hg
    simpa only [d258977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29351 (p : Pattern) (guard : d258978 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258977 p = 1 := by simpa only [d258978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29350 p hg
    simpa only [d258978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29352 (p : Pattern) (guard : d258979 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258921 p = 1 := by simpa only [d258979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29293 p hg
    simpa only [d258979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29353 (p : Pattern) (guard : d258980 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258979 p = 1 := by simpa only [d258980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d258980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258839 p = 1 := by simpa only [d258980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29154 p hg
    simpa only [d258980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29354 (p : Pattern) (guard : d258981 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258980 p = 1 := by simpa only [d258981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29353 p hg
    simpa only [d258981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29355 (p : Pattern) (guard : d258982 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258981 p = 1 := by simpa only [d258982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29354 p hg
    simpa only [d258982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29356 (p : Pattern) (guard : d258983 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258982 p = 1 := by simpa only [d258983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29355 p hg
    simpa only [d258983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29357 (p : Pattern) (guard : d258984 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258928 p = 1 := by simpa only [d258984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29300 p hg
    simpa only [d258984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29358 (p : Pattern) (guard : d258985 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258984 p = 1 := by simpa only [d258985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29357 p hg
    simpa only [d258985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258844 p = 1 := by simpa only [d258985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29159 p hg
    simpa only [d258985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29359 (p : Pattern) (guard : d258986 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258985 p = 1 := by simpa only [d258986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29358 p hg
    simpa only [d258986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29360 (p : Pattern) (guard : d258987 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258986 p = 1 := by simpa only [d258987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29359 p hg
    simpa only [d258987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29361 (p : Pattern) (guard : d258988 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258965 p = 1 := by simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29338 p hg
    simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29362 (p : Pattern) (guard : d258989 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258988 p = 1 := by simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29361 p hg
    simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258848 p = 1 := by simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29163 p hg
    simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29363 (p : Pattern) (guard : d258990 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258989 p = 1 := by simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29362 p hg
    simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29364 (p : Pattern) (guard : d258991 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258971 p = 1 := by simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29344 p hg
    simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29365 (p : Pattern) (guard : d258992 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258991 p = 1 := by simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29364 p hg
    simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29366 (p : Pattern) (guard : d258993 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258992 p = 1 := by simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29365 p hg
    simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29367 (p : Pattern) (guard : d258994 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258990 p = 1 := by simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29363 p hg
    simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258993 p = 1 := by simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29366 p hg
    simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29368 (p : Pattern) (guard : d258995 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d258987 p = 1 := by simpa only [d258995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29360 p hg
    simpa only [d258995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258994 p = 1 := by simpa only [d258995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29367 p hg
    simpa only [d258995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29369 (p : Pattern) (guard : d258996 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d258983 p = 1 := by simpa only [d258996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29356 p hg
    simpa only [d258996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258995 p = 1 := by simpa only [d258996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29368 p hg
    simpa only [d258996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29370 (p : Pattern) (guard : d258997 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258977 p = 1 := by simpa only [d258997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29350 p hg
    simpa only [d258997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258996 p = 1 := by simpa only [d258997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29369 p hg
    simpa only [d258997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29371 (p : Pattern) (guard : d258998 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258978 p = 1 := by simpa only [d258998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29351 p hg
    simpa only [d258998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258997 p = 1 := by simpa only [d258998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29370 p hg
    simpa only [d258998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29372 (p : Pattern) (guard : d258999 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258909 p = 1 := by simpa only [d258999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d258999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258782 p = 1 := by simpa only [d258999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29095 p hg
    simpa only [d258999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29373 (p : Pattern) (guard : d259000 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258999 p = 1 := by simpa only [d259000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29372 p hg
    simpa only [d259000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258790 p = 1 := by simpa only [d259000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29103 p hg
    simpa only [d259000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29374 (p : Pattern) (guard : d259001 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258998 p = 1 := by simpa only [d259001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29371 p hg
    simpa only [d259001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259000 p = 1 := by simpa only [d259001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29373 p hg
    simpa only [d259001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29375 (p : Pattern) (guard : d259002 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259001 p = 1 := by simpa only [d259002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29374 p hg
    simpa only [d259002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29376 (p : Pattern) (guard : d259003 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d258920 p = 1 := by simpa only [d259003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29292 p hg
    simpa only [d259003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259002 p = 1 := by simpa only [d259003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29375 p hg
    simpa only [d259003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29377 (p : Pattern) (guard : d1998 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29177 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29378 (p : Pattern) (guard : d258933 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29377 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29178 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29379 (p : Pattern) (guard : d258934 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29378 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29380 (p : Pattern) (guard : d258935 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29379 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29381 (p : Pattern) (guard : d258936 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29380 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29382 (p : Pattern) (guard : d258937 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29381 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29383 (p : Pattern) (guard : d258938 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29382 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29183 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29384 (p : Pattern) (guard : d258939 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29383 p hg
    simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29385 (p : Pattern) (guard : d258940 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29183 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29386 (p : Pattern) (guard : d258941 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29385 p hg
    simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29387 (p : Pattern) (guard : d258942 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29384 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29386 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29388 (p : Pattern) (guard : d258943 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29387 p hg
    simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29389 (p : Pattern) (guard : d258944 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258943 p = 1 := by simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29388 p hg
    simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29390 (p : Pattern) (guard : d258945 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258944 p = 1 := by simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29389 p hg
    simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29391 (p : Pattern) (guard : d258946 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258945 p = 1 := by simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29390 p hg
    simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29392 (p : Pattern) (guard : d258947 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258946 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29391 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258818 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29190 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29393 (p : Pattern) (guard : d258948 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29386 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28975 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29394 (p : Pattern) (guard : d258949 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29393 p hg
    simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29395 (p : Pattern) (guard : d258950 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258949 p = 1 := by simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29394 p hg
    simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29396 (p : Pattern) (guard : d258951 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258950 p = 1 := by simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29395 p hg
    simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29397 (p : Pattern) (guard : d258952 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258951 p = 1 := by simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29396 p hg
    simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29398 (p : Pattern) (guard : d258953 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258952 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29397 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28983 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29399 (p : Pattern) (guard : d258954 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258947 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29392 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258953 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29398 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29400 (p : Pattern) (guard : d258955 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258954 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29399 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258820 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29192 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29401 (p : Pattern) (guard : d258956 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258955 p = 1 := by simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29400 p hg
    simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29402 (p : Pattern) (guard : d258957 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258956 p = 1 := by simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29401 p hg
    simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29403 (p : Pattern) (guard : d258958 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258957 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29402 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258823 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29195 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29404 (p : Pattern) (guard : d258959 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258958 p = 1 := by simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29403 p hg
    simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258824 p = 1 := by simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29196 p hg
    simpa only [d258959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29405 (p : Pattern) (guard : d258960 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258959 p = 1 := by simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29404 p hg
    simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d258960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29406 (p : Pattern) (guard : d258961 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258960 p = 1 := by simpa only [d258961, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29405 p hg
    simpa only [d258961, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258961, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d258961, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29407 (p : Pattern) (guard : d258962 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258962, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d258962, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258961 p = 1 := by simpa only [d258962, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29406 p hg
    simpa only [d258962, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29408 (p : Pattern) (guard : d258963 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258962 p = 1 := by simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29407 p hg
    simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258828 p = 1 := by simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29200 p hg
    simpa only [d258963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29409 (p : Pattern) (guard : d258964 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258963 p = 1 := by simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29408 p hg
    simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29410 (p : Pattern) (guard : d258965 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258964 p = 1 := by simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29409 p hg
    simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29411 (p : Pattern) (guard : d258988 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258965 p = 1 := by simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29410 p hg
    simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29412 (p : Pattern) (guard : d258989 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258988 p = 1 := by simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29411 p hg
    simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258848 p = 1 := by simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29204 p hg
    simpa only [d258989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29413 (p : Pattern) (guard : d258990 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258989 p = 1 := by simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29412 p hg
    simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29414 (p : Pattern) (guard : d258969 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258828 p = 1 := by simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29200 p hg
    simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29415 (p : Pattern) (guard : d258970 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258969 p = 1 := by simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29414 p hg
    simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29416 (p : Pattern) (guard : d258971 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258970 p = 1 := by simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29415 p hg
    simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29417 (p : Pattern) (guard : d258991 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258971 p = 1 := by simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29416 p hg
    simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29418 (p : Pattern) (guard : d258992 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258991 p = 1 := by simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29417 p hg
    simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29419 (p : Pattern) (guard : d258993 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258992 p = 1 := by simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29418 p hg
    simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29420 (p : Pattern) (guard : d258994 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258990 p = 1 := by simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29413 p hg
    simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258993 p = 1 := by simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29419 p hg
    simpa only [d258994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29421 (p : Pattern) (guard : d259004 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258994 p = 1 := by simpa only [d259004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29420 p hg
    simpa only [d259004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29422 (p : Pattern) (guard : d259005 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259004 p = 1 := by simpa only [d259005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29421 p hg
    simpa only [d259005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29423 (p : Pattern) (guard : d259006 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259006, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259006, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259005 p = 1 := by simpa only [d259006, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29422 p hg
    simpa only [d259006, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29424 (p : Pattern) (guard : d259007 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259006 p = 1 := by simpa only [d259007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29423 p hg
    simpa only [d259007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29425 (p : Pattern) (guard : d258786 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258727 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29001 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29426 (p : Pattern) (guard : d258787 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258786 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29425 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29427 (p : Pattern) (guard : d258788 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258787 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29426 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29428 (p : Pattern) (guard : d258789 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258788 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29427 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29429 (p : Pattern) (guard : d259008 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258789 p = 1 := by simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29428 p hg
    simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29430 (p : Pattern) (guard : d259009 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259008 p = 1 := by simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29429 p hg
    simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29431 (p : Pattern) (guard : d259010 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259007 p = 1 := by simpa only [d259010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29424 p hg
    simpa only [d259010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259009 p = 1 := by simpa only [d259010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29430 p hg
    simpa only [d259010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29432 (p : Pattern) (guard : d259011 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259010 p = 1 := by simpa only [d259011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29431 p hg
    simpa only [d259011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29433 (p : Pattern) (guard : d259012 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259011 p = 1 := by simpa only [d259012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29432 p hg
    simpa only [d259012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29434 (p : Pattern) (guard : d259013 p = 1) : d47768 p ≤ (-1 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259003 p = 1 := by simpa only [d259013, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29376 p hg
    simpa only [d259013, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259012 p = 1 := by simpa only [d259013, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29433 p hg
    simpa only [d259013, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29435 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29436 (p : Pattern) (guard : d258933 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29435 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29218 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29437 (p : Pattern) (guard : d258934 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29436 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29438 (p : Pattern) (guard : d258935 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29437 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29439 (p : Pattern) (guard : d258936 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29438 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29440 (p : Pattern) (guard : d258937 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29439 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29441 (p : Pattern) (guard : d258938 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29440 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29223 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29442 (p : Pattern) (guard : d258939 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29441 p hg
    simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29443 (p : Pattern) (guard : d258940 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29223 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29444 (p : Pattern) (guard : d258941 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29443 p hg
    simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29445 (p : Pattern) (guard : d258942 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29442 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29444 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29446 (p : Pattern) (guard : d259014 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258942 p = 1 := by simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29445 p hg
    simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29447 (p : Pattern) (guard : d258943 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29315 p hg
    simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29448 (p : Pattern) (guard : d259015 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259014 p = 1 := by simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29446 p hg
    simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258943 p = 1 := by simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29447 p hg
    simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29449 (p : Pattern) (guard : d1998 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29231 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29450 (p : Pattern) (guard : d258933 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29449 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29232 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29451 (p : Pattern) (guard : d258934 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29450 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29452 (p : Pattern) (guard : d258935 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29451 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29453 (p : Pattern) (guard : d258936 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29452 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29454 (p : Pattern) (guard : d258937 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29453 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29455 (p : Pattern) (guard : d258938 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29454 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29456 (p : Pattern) (guard : d258939 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29455 p hg
    simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29457 (p : Pattern) (guard : d258940 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29458 (p : Pattern) (guard : d258941 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29457 p hg
    simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29459 (p : Pattern) (guard : d258942 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29456 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29458 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29460 (p : Pattern) (guard : d258943 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29459 p hg
    simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29461 (p : Pattern) (guard : d258944 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258943 p = 1 := by simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29460 p hg
    simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29462 (p : Pattern) (guard : d259016 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259015 p = 1 := by simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29448 p hg
    simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258944 p = 1 := by simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29461 p hg
    simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29463 (p : Pattern) (guard : d259017 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259016 p = 1 := by simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29462 p hg
    simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29464 (p : Pattern) (guard : d259018 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259017 p = 1 := by simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29463 p hg
    simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258872 p = 1 := by simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29465 (p : Pattern) (guard : d258948 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29444 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29030 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29466 (p : Pattern) (guard : d259019 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258948 p = 1 := by simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29465 p hg
    simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29467 (p : Pattern) (guard : d258949 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29321 p hg
    simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29468 (p : Pattern) (guard : d259020 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259019 p = 1 := by simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258949 p = 1 := by simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29467 p hg
    simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29469 (p : Pattern) (guard : d258948 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29458 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29470 (p : Pattern) (guard : d258949 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29471 (p : Pattern) (guard : d258950 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258949 p = 1 := by simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29470 p hg
    simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29472 (p : Pattern) (guard : d259021 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259020 p = 1 := by simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29468 p hg
    simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258950 p = 1 := by simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29471 p hg
    simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29473 (p : Pattern) (guard : d259022 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259021 p = 1 := by simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29474 (p : Pattern) (guard : d259023 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259022 p = 1 := by simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29473 p hg
    simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258746 p = 1 := by simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29475 (p : Pattern) (guard : d259024 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259018 p = 1 := by simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29464 p hg
    simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259023 p = 1 := by simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29474 p hg
    simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29476 (p : Pattern) (guard : d259025 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259024 p = 1 := by simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29475 p hg
    simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258874 p = 1 := by simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29246 p hg
    simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29477 (p : Pattern) (guard : d259026 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259025 p = 1 := by simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29478 (p : Pattern) (guard : d259027 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259026 p = 1 := by simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29477 p hg
    simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29479 (p : Pattern) (guard : d259028 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259027 p = 1 := by simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29478 p hg
    simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258877 p = 1 := by simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29249 p hg
    simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29480 (p : Pattern) (guard : d259029 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259028 p = 1 := by simpa only [d259029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29479 p hg
    simpa only [d259029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258878 p = 1 := by simpa only [d259029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29250 p hg
    simpa only [d259029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29481 (p : Pattern) (guard : d259030 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259029 p = 1 := by simpa only [d259030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29480 p hg
    simpa only [d259030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29482 (p : Pattern) (guard : d259031 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259030 p = 1 := by simpa only [d259031, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29481 p hg
    simpa only [d259031, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259031, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259031, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29483 (p : Pattern) (guard : d259032 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259032, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259032, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259031 p = 1 := by simpa only [d259032, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29482 p hg
    simpa only [d259032, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29484 (p : Pattern) (guard : d259033 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259032 p = 1 := by simpa only [d259033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29483 p hg
    simpa only [d259033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258882 p = 1 := by simpa only [d259033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d259033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29485 (p : Pattern) (guard : d259034 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259033 p = 1 := by simpa only [d259034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29484 p hg
    simpa only [d259034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29486 (p : Pattern) (guard : d259035 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259034 p = 1 := by simpa only [d259035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29485 p hg
    simpa only [d259035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29487 (p : Pattern) (guard : d259036 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259035 p = 1 := by simpa only [d259036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29486 p hg
    simpa only [d259036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29488 (p : Pattern) (guard : d259037 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259036 p = 1 := by simpa only [d259037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d259037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258886 p = 1 := by simpa only [d259037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29258 p hg
    simpa only [d259037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29489 (p : Pattern) (guard : d259038 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259037 p = 1 := by simpa only [d259038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29488 p hg
    simpa only [d259038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29490 (p : Pattern) (guard : d259039 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258882 p = 1 := by simpa only [d259039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d259039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29491 (p : Pattern) (guard : d259040 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259039 p = 1 := by simpa only [d259040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29490 p hg
    simpa only [d259040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29492 (p : Pattern) (guard : d259041 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259040 p = 1 := by simpa only [d259041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29491 p hg
    simpa only [d259041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29493 (p : Pattern) (guard : d259042 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259041 p = 1 := by simpa only [d259042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d259042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29494 (p : Pattern) (guard : d259043 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259042 p = 1 := by simpa only [d259043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29493 p hg
    simpa only [d259043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29495 (p : Pattern) (guard : d259044 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259043 p = 1 := by simpa only [d259044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29494 p hg
    simpa only [d259044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29496 (p : Pattern) (guard : d259045 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259038 p = 1 := by simpa only [d259045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29489 p hg
    simpa only [d259045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259044 p = 1 := by simpa only [d259045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29495 p hg
    simpa only [d259045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29497 (p : Pattern) (guard : d259046 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259045 p = 1 := by simpa only [d259046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29496 p hg
    simpa only [d259046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29498 (p : Pattern) (guard : d259047 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259046 p = 1 := by simpa only [d259047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29497 p hg
    simpa only [d259047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29499 (p : Pattern) (guard : d259048 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259048, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259048, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259047 p = 1 := by simpa only [d259048, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29498 p hg
    simpa only [d259048, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
