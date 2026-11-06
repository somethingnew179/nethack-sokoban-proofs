import NetHack.Soko22Hazard87.Compare151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38000 (p : Pattern) (guard : d257237 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257236 p = 1 := by simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37999 p hg
    simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38001 (p : Pattern) (guard : d257238 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257237 p = 1 := by simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38000 p hg
    simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38002 (p : Pattern) (guard : d0 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38003 (p : Pattern) (guard : d257239 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257238 p = 1 := by simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38001 p hg
    simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38004 (p : Pattern) (guard : d257240 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257239 p = 1 := by simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38003 p hg
    simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38005 (p : Pattern) (guard : d257241 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257240 p = 1 := by simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38004 p hg
    simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38006 (p : Pattern) (guard : d0 p = 1) : d50429 p ≤ (2 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38007 (p : Pattern) (guard : d257242 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257241 p = 1 := by simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38005 p hg
    simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38008 (p : Pattern) (guard : d257243 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257242 p = 1 := by simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38007 p hg
    simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38009 (p : Pattern) (guard : d257244 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257243 p = 1 := by simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38008 p hg
    simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38010 (p : Pattern) (guard : d257245 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257244 p = 1 := by simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38009 p hg
    simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38011 (p : Pattern) (guard : d257246 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257245 p = 1 := by simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38010 p hg
    simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38012 (p : Pattern) (guard : d257247 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257246 p = 1 := by simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38011 p hg
    simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38013 (p : Pattern) (guard : d257248 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257247 p = 1 := by simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38012 p hg
    simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38014 (p : Pattern) (guard : d257532 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257248 p = 1 := by simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38013 p hg
    simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38015 (p : Pattern) (guard : d257533 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257532 p = 1 := by simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38014 p hg
    simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38016 (p : Pattern) (guard : d257534 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257533 p = 1 := by simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38015 p hg
    simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38017 (p : Pattern) (guard : d257535 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257534 p = 1 := by simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38016 p hg
    simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38018 (p : Pattern) (guard : d257536 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257535 p = 1 := by simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38017 p hg
    simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38019 (p : Pattern) (guard : d257537 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257536 p = 1 := by simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38018 p hg
    simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38020 (p : Pattern) (guard : d259889 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257537 p = 1 := by simpa only [d259889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38019 p hg
    simpa only [d259889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d259889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38021 (p : Pattern) (guard : d259890 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259889 p = 1 := by simpa only [d259890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38020 p hg
    simpa only [d259890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d259890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38022 (p : Pattern) (guard : d259891 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259890 p = 1 := by simpa only [d259891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38021 p hg
    simpa only [d259891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d259891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38023 (p : Pattern) (guard : d0 p = 1) : d50491 p ≤ (2 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38024 (p : Pattern) (guard : d259892 p = 1) : d50492 p ≤ (2 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259891 p = 1 := by simpa only [d259892, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38022 p hg
    simpa only [d259892, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259892, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38023 p hg
    simpa only [d259892, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38025 (p : Pattern) (guard : d259893 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d259888 p = 1 := by simpa only [d259893, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37953 p hg
    simpa only [d259893, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259892 p = 1 := by simpa only [d259893, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38024 p hg
    simpa only [d259893, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38026 (p : Pattern) (guard : d259894 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d259894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259893 p = 1 := by simpa only [d259894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38025 p hg
    simpa only [d259894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38027 (p : Pattern) (guard : d259895 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d259895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259894 p = 1 := by simpa only [d259895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38026 p hg
    simpa only [d259895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38028 (p : Pattern) (guard : d259896 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d259896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259895 p = 1 := by simpa only [d259896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38027 p hg
    simpa only [d259896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38029 (p : Pattern) (guard : d259897 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d259897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259896 p = 1 := by simpa only [d259897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38028 p hg
    simpa only [d259897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38030 (p : Pattern) (guard : d259898 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d259898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259897 p = 1 := by simpa only [d259898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38029 p hg
    simpa only [d259898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38031 (p : Pattern) (guard : d259899 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d259899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259898 p = 1 := by simpa only [d259899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38030 p hg
    simpa only [d259899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38032 (p : Pattern) (guard : d130 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38033 (p : Pattern) (guard : d33213 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38032 p hg
    simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38034 (p : Pattern) (guard : d285865 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38033 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38035 (p : Pattern) (guard : d285866 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38034 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38036 (p : Pattern) (guard : d285867 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38035 p hg
    simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38037 (p : Pattern) (guard : d285868 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38036 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37831 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38038 (p : Pattern) (guard : d285869 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38037 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37833 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38039 (p : Pattern) (guard : d285870 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38038 p hg
    simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38040 (p : Pattern) (guard : d285871 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38039 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37836 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38041 (p : Pattern) (guard : d285872 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38040 p hg
    simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38042 (p : Pattern) (guard : d285873 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285872 p = 1 := by simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38041 p hg
    simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38043 (p : Pattern) (guard : d285874 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285873 p = 1 := by simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38042 p hg
    simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38044 (p : Pattern) (guard : d285875 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285874 p = 1 := by simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38043 p hg
    simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38045 (p : Pattern) (guard : d285876 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285875 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38044 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37845 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38046 (p : Pattern) (guard : d285877 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285876 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38045 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257193 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37847 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38047 (p : Pattern) (guard : d285878 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d285877 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38046 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257194 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37848 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38048 (p : Pattern) (guard : d285879 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285878 p = 1 := by simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38047 p hg
    simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38049 (p : Pattern) (guard : d285880 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285879 p = 1 := by simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38048 p hg
    simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38050 (p : Pattern) (guard : d285881 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38049 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257197 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37851 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38051 (p : Pattern) (guard : d285882 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285881 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38050 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257198 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37853 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38052 (p : Pattern) (guard : d285883 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285882 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38051 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38053 (p : Pattern) (guard : d285884 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285883 p = 1 := by simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38052 p hg
    simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38054 (p : Pattern) (guard : d285885 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285884 p = 1 := by simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38053 p hg
    simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38055 (p : Pattern) (guard : d285886 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38054 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257202 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37858 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38056 (p : Pattern) (guard : d285887 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285886 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38055 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38057 (p : Pattern) (guard : d285888 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285887 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38056 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38058 (p : Pattern) (guard : d285889 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285888 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38057 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38059 (p : Pattern) (guard : d285890 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285889 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38058 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257206 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37862 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38060 (p : Pattern) (guard : d285951 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285890 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38059 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38061 (p : Pattern) (guard : d285952 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285951 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38060 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38062 (p : Pattern) (guard : d285953 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285952 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38061 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38063 (p : Pattern) (guard : d285954 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285953 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38062 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38064 (p : Pattern) (guard : d285955 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285954 p = 1 := by simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38063 p hg
    simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38065 (p : Pattern) (guard : d285880 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285879 p = 1 := by simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38048 p hg
    simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38066 (p : Pattern) (guard : d285881 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38065 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257197 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37871 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38067 (p : Pattern) (guard : d285882 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285881 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38066 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257198 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37873 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38068 (p : Pattern) (guard : d285883 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285882 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38067 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38069 (p : Pattern) (guard : d285884 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285883 p = 1 := by simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38068 p hg
    simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38070 (p : Pattern) (guard : d285885 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285884 p = 1 := by simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38069 p hg
    simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38071 (p : Pattern) (guard : d285886 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38070 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257202 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37877 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38072 (p : Pattern) (guard : d285887 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285886 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38071 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38073 (p : Pattern) (guard : d285888 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285887 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38072 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38074 (p : Pattern) (guard : d285889 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285888 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38073 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38075 (p : Pattern) (guard : d285890 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285889 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38074 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257206 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37881 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38076 (p : Pattern) (guard : d285951 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285890 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38075 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38077 (p : Pattern) (guard : d285952 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285951 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38076 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38078 (p : Pattern) (guard : d285953 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285952 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38077 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38079 (p : Pattern) (guard : d285954 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285953 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38078 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38080 (p : Pattern) (guard : d285896 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285888 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38057 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38081 (p : Pattern) (guard : d285897 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285896 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38080 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257213 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37887 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38082 (p : Pattern) (guard : d285958 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285897 p = 1 := by simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38081 p hg
    simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38083 (p : Pattern) (guard : d285959 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285958 p = 1 := by simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38082 p hg
    simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38084 (p : Pattern) (guard : d285960 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285959 p = 1 := by simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38083 p hg
    simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38085 (p : Pattern) (guard : d285961 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285960 p = 1 := by simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38084 p hg
    simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38086 (p : Pattern) (guard : d285962 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d285954 p = 1 := by simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38079 p hg
    simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285961 p = 1 := by simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38085 p hg
    simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38087 (p : Pattern) (guard : d285963 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d285955 p = 1 := by simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38064 p hg
    simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285962 p = 1 := by simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38086 p hg
    simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38088 (p : Pattern) (guard : d285964 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285963 p = 1 := by simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38087 p hg
    simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38089 (p : Pattern) (guard : d287251 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d285964 p = 1 := by simpa only [d287251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38088 p hg
    simpa only [d287251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d287251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38090 (p : Pattern) (guard : d287252 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d287252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287251 p = 1 := by simpa only [d287252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38089 p hg
    simpa only [d287252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38091 (p : Pattern) (guard : d130 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare38092 (p : Pattern) (guard : d33213 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38091 p hg
    simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38093 (p : Pattern) (guard : d285865 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38092 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38094 (p : Pattern) (guard : d285866 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38093 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38095 (p : Pattern) (guard : d285867 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38094 p hg
    simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38096 (p : Pattern) (guard : d285868 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38095 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37911 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38097 (p : Pattern) (guard : d285869 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38096 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37913 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38098 (p : Pattern) (guard : d285870 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38097 p hg
    simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38099 (p : Pattern) (guard : d285871 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38098 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37916 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38100 (p : Pattern) (guard : d285872 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38099 p hg
    simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38101 (p : Pattern) (guard : d285873 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285872 p = 1 := by simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38100 p hg
    simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38102 (p : Pattern) (guard : d285874 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285873 p = 1 := by simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38101 p hg
    simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38103 (p : Pattern) (guard : d285875 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285874 p = 1 := by simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38102 p hg
    simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38104 (p : Pattern) (guard : d285876 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285875 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38103 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37925 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38105 (p : Pattern) (guard : d285877 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285876 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38104 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257193 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37927 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38106 (p : Pattern) (guard : d285878 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d285877 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38105 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257194 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37928 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38107 (p : Pattern) (guard : d285879 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285878 p = 1 := by simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38106 p hg
    simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38108 (p : Pattern) (guard : d285880 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285879 p = 1 := by simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38107 p hg
    simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38109 (p : Pattern) (guard : d285881 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38108 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257197 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37931 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38110 (p : Pattern) (guard : d285882 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285881 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38109 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257198 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37933 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38111 (p : Pattern) (guard : d285883 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285882 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38110 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38112 (p : Pattern) (guard : d285884 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285883 p = 1 := by simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38111 p hg
    simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38113 (p : Pattern) (guard : d285885 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285884 p = 1 := by simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38112 p hg
    simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38114 (p : Pattern) (guard : d285886 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38113 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257202 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37938 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38115 (p : Pattern) (guard : d285887 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285886 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38114 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38116 (p : Pattern) (guard : d285888 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285887 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38115 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38117 (p : Pattern) (guard : d285896 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285888 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38116 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38118 (p : Pattern) (guard : d285897 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285896 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38117 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257213 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37942 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38119 (p : Pattern) (guard : d285958 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285897 p = 1 := by simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38118 p hg
    simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38120 (p : Pattern) (guard : d285959 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285958 p = 1 := by simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38119 p hg
    simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38121 (p : Pattern) (guard : d285960 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285959 p = 1 := by simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38120 p hg
    simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38122 (p : Pattern) (guard : d285961 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285960 p = 1 := by simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38121 p hg
    simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38123 (p : Pattern) (guard : d287253 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287253, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d287253, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285961 p = 1 := by simpa only [d287253, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38122 p hg
    simpa only [d287253, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38124 (p : Pattern) (guard : d287254 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d287254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287253 p = 1 := by simpa only [d287254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38123 p hg
    simpa only [d287254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38125 (p : Pattern) (guard : d287255 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d287254 p = 1 := by simpa only [d287255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38124 p hg
    simpa only [d287255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d287255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38126 (p : Pattern) (guard : d287256 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d287255 p = 1 := by simpa only [d287256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38125 p hg
    simpa only [d287256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d287256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38127 (p : Pattern) (guard : d287257 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d287256 p = 1 := by simpa only [d287257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38126 p hg
    simpa only [d287257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d287257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38128 (p : Pattern) (guard : d287258 p = 1) : d50390 p ≤ (2 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d287252 p = 1 := by simpa only [d287258, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38090 p hg
    simpa only [d287258, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287257 p = 1 := by simpa only [d287258, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38127 p hg
    simpa only [d287258, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38129 (p : Pattern) (guard : d130 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare38130 (p : Pattern) (guard : d33213 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38129 p hg
    simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38131 (p : Pattern) (guard : d285865 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38130 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38132 (p : Pattern) (guard : d285866 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38131 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38133 (p : Pattern) (guard : d285867 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38132 p hg
    simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38134 (p : Pattern) (guard : d285868 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38133 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37966 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38135 (p : Pattern) (guard : d285869 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38134 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37968 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38136 (p : Pattern) (guard : d285870 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38135 p hg
    simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38137 (p : Pattern) (guard : d285871 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38136 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37971 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38138 (p : Pattern) (guard : d285915 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285871 p = 1 := by simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38137 p hg
    simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38139 (p : Pattern) (guard : d285872 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38040 p hg
    simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38140 (p : Pattern) (guard : d285916 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285915 p = 1 := by simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38138 p hg
    simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285872 p = 1 := by simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38139 p hg
    simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38141 (p : Pattern) (guard : d130 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare38142 (p : Pattern) (guard : d33213 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38141 p hg
    simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38143 (p : Pattern) (guard : d285865 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38142 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38144 (p : Pattern) (guard : d285866 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38143 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38145 (p : Pattern) (guard : d285867 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38144 p hg
    simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38146 (p : Pattern) (guard : d285868 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38145 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37983 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38147 (p : Pattern) (guard : d285869 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38146 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37985 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38148 (p : Pattern) (guard : d285870 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38147 p hg
    simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38149 (p : Pattern) (guard : d285871 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38148 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37988 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38150 (p : Pattern) (guard : d285872 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38149 p hg
    simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38151 (p : Pattern) (guard : d285873 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285872 p = 1 := by simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38152 (p : Pattern) (guard : d285917 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d285916 p = 1 := by simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38140 p hg
    simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285873 p = 1 := by simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38151 p hg
    simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38153 (p : Pattern) (guard : d285918 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285917 p = 1 := by simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38154 (p : Pattern) (guard : d285919 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285918 p = 1 := by simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38153 p hg
    simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257233 p = 1 := by simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37995 p hg
    simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38155 (p : Pattern) (guard : d285920 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285919 p = 1 := by simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38154 p hg
    simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257234 p = 1 := by simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37997 p hg
    simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38156 (p : Pattern) (guard : d285921 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d285920 p = 1 := by simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38155 p hg
    simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257235 p = 1 := by simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37998 p hg
    simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38157 (p : Pattern) (guard : d285922 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285921 p = 1 := by simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38156 p hg
    simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38158 (p : Pattern) (guard : d285923 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285922 p = 1 := by simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38157 p hg
    simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38159 (p : Pattern) (guard : d285924 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285923 p = 1 := by simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38158 p hg
    simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257238 p = 1 := by simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38001 p hg
    simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38160 (p : Pattern) (guard : d285925 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285924 p = 1 := by simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38159 p hg
    simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257239 p = 1 := by simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38003 p hg
    simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38161 (p : Pattern) (guard : d285926 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285925 p = 1 := by simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38160 p hg
    simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38162 (p : Pattern) (guard : d285927 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285926 p = 1 := by simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38161 p hg
    simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38163 (p : Pattern) (guard : d285928 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285927 p = 1 := by simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38162 p hg
    simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38164 (p : Pattern) (guard : d285929 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285928 p = 1 := by simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38163 p hg
    simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257243 p = 1 := by simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38008 p hg
    simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38165 (p : Pattern) (guard : d285930 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285929 p = 1 := by simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38164 p hg
    simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38166 (p : Pattern) (guard : d285931 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285930 p = 1 := by simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38165 p hg
    simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38167 (p : Pattern) (guard : d285932 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285931 p = 1 := by simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38166 p hg
    simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38168 (p : Pattern) (guard : d285933 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285932 p = 1 := by simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38167 p hg
    simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257247 p = 1 := by simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38012 p hg
    simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38169 (p : Pattern) (guard : d287259 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d287259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285933 p = 1 := by simpa only [d287259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38168 p hg
    simpa only [d287259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38170 (p : Pattern) (guard : d287260 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287259 p = 1 := by simpa only [d287260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38169 p hg
    simpa only [d287260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d287260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38171 (p : Pattern) (guard : d287261 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d287261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287260 p = 1 := by simpa only [d287261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38170 p hg
    simpa only [d287261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38172 (p : Pattern) (guard : d287262 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d287262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287261 p = 1 := by simpa only [d287262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38171 p hg
    simpa only [d287262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38173 (p : Pattern) (guard : d287263 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287263, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d287263, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287262 p = 1 := by simpa only [d287263, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38172 p hg
    simpa only [d287263, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38174 (p : Pattern) (guard : d287264 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d287264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287263 p = 1 := by simpa only [d287264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38173 p hg
    simpa only [d287264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38175 (p : Pattern) (guard : d287265 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d287264 p = 1 := by simpa only [d287265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38174 p hg
    simpa only [d287265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d287265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38176 (p : Pattern) (guard : d287266 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d287265 p = 1 := by simpa only [d287266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38175 p hg
    simpa only [d287266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d287266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38177 (p : Pattern) (guard : d287267 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d287266 p = 1 := by simpa only [d287267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38176 p hg
    simpa only [d287267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d287267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38178 (p : Pattern) (guard : d287268 p = 1) : d50492 p ≤ (2 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d287267 p = 1 := by simpa only [d287268, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38177 p hg
    simpa only [d287268, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d287268, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38023 p hg
    simpa only [d287268, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38179 (p : Pattern) (guard : d287269 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d287258 p = 1 := by simpa only [d287269, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38128 p hg
    simpa only [d287269, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287268 p = 1 := by simpa only [d287269, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38178 p hg
    simpa only [d287269, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38180 (p : Pattern) (guard : d287270 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d287270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287269 p = 1 := by simpa only [d287270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38179 p hg
    simpa only [d287270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38181 (p : Pattern) (guard : d287271 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d287271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287270 p = 1 := by simpa only [d287271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38180 p hg
    simpa only [d287271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38182 (p : Pattern) (guard : d287272 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d287272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287271 p = 1 := by simpa only [d287272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38181 p hg
    simpa only [d287272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38183 (p : Pattern) (guard : d287273 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d287273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287272 p = 1 := by simpa only [d287273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38182 p hg
    simpa only [d287273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38184 (p : Pattern) (guard : d287274 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d287274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287273 p = 1 := by simpa only [d287274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38183 p hg
    simpa only [d287274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38185 (p : Pattern) (guard : d287275 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d287275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287274 p = 1 := by simpa only [d287275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38184 p hg
    simpa only [d287275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38186 (p : Pattern) (guard : d287276 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d259899 p = 1 := by simpa only [d287276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38031 p hg
    simpa only [d287276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d287275 p = 1 := by simpa only [d287276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38185 p hg
    simpa only [d287276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38187 (p : Pattern) (guard : d1520 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38188 (p : Pattern) (guard : d33554 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38187 p hg
    simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38189 (p : Pattern) (guard : d286611 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38188 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38190 (p : Pattern) (guard : d286612 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38189 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38191 (p : Pattern) (guard : d286613 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38190 p hg
    simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38192 (p : Pattern) (guard : d316227 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38191 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38036 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38193 (p : Pattern) (guard : d534 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38194 (p : Pattern) (guard : d33559 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38193 p hg
    simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38195 (p : Pattern) (guard : d316228 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38194 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38196 (p : Pattern) (guard : d316229 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38195 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38197 (p : Pattern) (guard : d316230 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38196 p hg
    simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38198 (p : Pattern) (guard : d316231 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38197 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37831 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38199 (p : Pattern) (guard : d316232 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38192 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38198 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38200 (p : Pattern) (guard : d316233 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38199 p hg
    simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38201 (p : Pattern) (guard : d316234 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38200 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38039 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38202 (p : Pattern) (guard : d316235 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38201 p hg
    simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38203 (p : Pattern) (guard : d316236 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316235 p = 1 := by simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38202 p hg
    simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38204 (p : Pattern) (guard : d316237 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316236 p = 1 := by simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38203 p hg
    simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38205 (p : Pattern) (guard : d316238 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316237 p = 1 := by simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38204 p hg
    simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38206 (p : Pattern) (guard : d316239 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316238 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38205 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285875 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38044 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38207 (p : Pattern) (guard : d285991 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38037 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38208 (p : Pattern) (guard : d285992 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38207 p hg
    simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38209 (p : Pattern) (guard : d285993 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38208 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37836 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38210 (p : Pattern) (guard : d285994 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38209 p hg
    simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38211 (p : Pattern) (guard : d285995 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285994 p = 1 := by simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38210 p hg
    simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38212 (p : Pattern) (guard : d285996 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285995 p = 1 := by simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38211 p hg
    simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38213 (p : Pattern) (guard : d285997 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285996 p = 1 := by simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38212 p hg
    simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38214 (p : Pattern) (guard : d285998 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285997 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38213 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37845 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38215 (p : Pattern) (guard : d316240 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316239 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38206 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285998 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38214 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38216 (p : Pattern) (guard : d316241 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316240 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38215 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285877 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38046 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38217 (p : Pattern) (guard : d316242 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316241 p = 1 := by simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38216 p hg
    simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38218 (p : Pattern) (guard : d316243 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316242 p = 1 := by simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38217 p hg
    simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38219 (p : Pattern) (guard : d316244 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316243 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38218 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285880 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38049 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38220 (p : Pattern) (guard : d286105 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38049 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38221 (p : Pattern) (guard : d316315 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38219 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286105 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38222 (p : Pattern) (guard : d316316 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316315 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38221 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38223 (p : Pattern) (guard : d316317 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316316 p = 1 := by simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38222 p hg
    simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38224 (p : Pattern) (guard : d316318 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316317 p = 1 := by simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38223 p hg
    simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38225 (p : Pattern) (guard : d286110 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286105 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38226 (p : Pattern) (guard : d286111 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286110 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38225 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38227 (p : Pattern) (guard : d286112 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286111 p = 1 := by simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38226 p hg
    simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38228 (p : Pattern) (guard : d286113 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286112 p = 1 := by simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38227 p hg
    simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38229 (p : Pattern) (guard : d316319 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38224 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286113 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38228 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38230 (p : Pattern) (guard : d316320 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316319 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38229 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38231 (p : Pattern) (guard : d316321 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316320 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38230 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38232 (p : Pattern) (guard : d316322 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316321 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38231 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38233 (p : Pattern) (guard : d286118 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286113 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38228 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38234 (p : Pattern) (guard : d286119 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286118 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38233 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38235 (p : Pattern) (guard : d286120 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286119 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38234 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38236 (p : Pattern) (guard : d286121 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286120 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38235 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38237 (p : Pattern) (guard : d316323 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316322 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38232 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286121 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38236 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38238 (p : Pattern) (guard : d316324 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316323 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38237 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38239 (p : Pattern) (guard : d316325 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316324 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38238 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38240 (p : Pattern) (guard : d316326 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316325 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38239 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38241 (p : Pattern) (guard : d316327 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316326 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38240 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38242 (p : Pattern) (guard : d316328 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316327 p = 1 := by simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38241 p hg
    simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38243 (p : Pattern) (guard : d316243 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316242 p = 1 := by simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38217 p hg
    simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38244 (p : Pattern) (guard : d316244 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316243 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38243 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285880 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38065 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38245 (p : Pattern) (guard : d286105 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38065 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38246 (p : Pattern) (guard : d316315 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38244 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286105 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38247 (p : Pattern) (guard : d316316 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316315 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38246 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38248 (p : Pattern) (guard : d316317 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316316 p = 1 := by simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38249 (p : Pattern) (guard : d316318 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316317 p = 1 := by simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38248 p hg
    simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
