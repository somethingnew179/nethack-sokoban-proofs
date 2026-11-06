import NetHack.Soko22Hazard87.Compare130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32750 (p : Pattern) (guard : d294895 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294894 p = 1 := by simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32749 p hg
    simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32751 (p : Pattern) (guard : d294896 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294895 p = 1 := by simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32750 p hg
    simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32752 (p : Pattern) (guard : d294897 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294896 p = 1 := by simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32751 p hg
    simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32753 (p : Pattern) (guard : d294898 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294897 p = 1 := by simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32752 p hg
    simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32754 (p : Pattern) (guard : d294899 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294892 p = 1 := by simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32747 p hg
    simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294898 p = 1 := by simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32753 p hg
    simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32755 (p : Pattern) (guard : d294900 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d294869 p = 1 := by simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32735 p hg
    simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294899 p = 1 := by simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32754 p hg
    simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32756 (p : Pattern) (guard : d294901 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d294860 p = 1 := by simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32726 p hg
    simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294900 p = 1 := by simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32755 p hg
    simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32757 (p : Pattern) (guard : d294903 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294853 p = 1 := by simpa only [d294903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32664 p hg
    simpa only [d294903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32758 (p : Pattern) (guard : d294904 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294855 p = 1 := by simpa only [d294904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32666 p hg
    simpa only [d294904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32759 (p : Pattern) (guard : d294905 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294903 p = 1 := by simpa only [d294905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32757 p hg
    simpa only [d294905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294904 p = 1 := by simpa only [d294905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32758 p hg
    simpa only [d294905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32760 (p : Pattern) (guard : d294906 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294905 p = 1 := by simpa only [d294906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32759 p hg
    simpa only [d294906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32761 (p : Pattern) (guard : d294907 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294906 p = 1 := by simpa only [d294907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32760 p hg
    simpa only [d294907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32762 (p : Pattern) (guard : d294908 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294907 p = 1 := by simpa only [d294908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32761 p hg
    simpa only [d294908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32763 (p : Pattern) (guard : d294909 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294862 p = 1 := by simpa only [d294909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32673 p hg
    simpa only [d294909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32764 (p : Pattern) (guard : d294910 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294865 p = 1 := by simpa only [d294910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d294910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32765 (p : Pattern) (guard : d294911 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294909 p = 1 := by simpa only [d294911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32763 p hg
    simpa only [d294911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294910 p = 1 := by simpa only [d294911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32764 p hg
    simpa only [d294911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32766 (p : Pattern) (guard : d294912 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294911 p = 1 := by simpa only [d294912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32765 p hg
    simpa only [d294912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32767 (p : Pattern) (guard : d294913 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294912 p = 1 := by simpa only [d294913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32766 p hg
    simpa only [d294913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32768 (p : Pattern) (guard : d294914 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294889 p = 1 := by simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32769 (p : Pattern) (guard : d294915 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294914 p = 1 := by simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32768 p hg
    simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294842 p = 1 := by simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32653 p hg
    simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32770 (p : Pattern) (guard : d294916 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294915 p = 1 := by simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32769 p hg
    simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32771 (p : Pattern) (guard : d294917 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294895 p = 1 := by simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32711 p hg
    simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32772 (p : Pattern) (guard : d294918 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294917 p = 1 := by simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32771 p hg
    simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32773 (p : Pattern) (guard : d294919 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294918 p = 1 := by simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32772 p hg
    simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32774 (p : Pattern) (guard : d294920 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294916 p = 1 := by simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32770 p hg
    simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294919 p = 1 := by simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32773 p hg
    simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32775 (p : Pattern) (guard : d294921 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d294913 p = 1 := by simpa only [d294921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32767 p hg
    simpa only [d294921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294920 p = 1 := by simpa only [d294921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32774 p hg
    simpa only [d294921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32776 (p : Pattern) (guard : d294922 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d294908 p = 1 := by simpa only [d294922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32762 p hg
    simpa only [d294922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294921 p = 1 := by simpa only [d294922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32775 p hg
    simpa only [d294922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32777 (p : Pattern) (guard : d294923 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294901 p = 1 := by simpa only [d294923, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32756 p hg
    simpa only [d294923, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294922 p = 1 := by simpa only [d294923, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32776 p hg
    simpa only [d294923, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32778 (p : Pattern) (guard : d294924 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294902 p = 1 := by simpa only [d294924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32718 p hg
    simpa only [d294924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294923 p = 1 := by simpa only [d294924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32777 p hg
    simpa only [d294924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32779 (p : Pattern) (guard : d294925 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294833 p = 1 := by simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32619 p hg
    simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32780 (p : Pattern) (guard : d294926 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294925 p = 1 := by simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32779 p hg
    simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32781 (p : Pattern) (guard : d294927 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294926 p = 1 := by simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32780 p hg
    simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32782 (p : Pattern) (guard : d294928 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294927 p = 1 := by simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32781 p hg
    simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32783 (p : Pattern) (guard : d294929 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294928 p = 1 := by simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32782 p hg
    simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32784 (p : Pattern) (guard : d294930 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294838 p = 1 := by simpa only [d294930, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32652 p hg
    simpa only [d294930, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294929 p = 1 := by simpa only [d294930, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32783 p hg
    simpa only [d294930, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32785 (p : Pattern) (guard : d294925 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294833 p = 1 := by simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32647 p hg
    simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32786 (p : Pattern) (guard : d294926 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294925 p = 1 := by simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32785 p hg
    simpa only [d294926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32787 (p : Pattern) (guard : d294927 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294926 p = 1 := by simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32786 p hg
    simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32788 (p : Pattern) (guard : d294928 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294927 p = 1 := by simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32787 p hg
    simpa only [d294928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32789 (p : Pattern) (guard : d294929 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294928 p = 1 := by simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32788 p hg
    simpa only [d294929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32790 (p : Pattern) (guard : d294931 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294843 p = 1 := by simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32654 p hg
    simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32791 (p : Pattern) (guard : d294932 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294931 p = 1 := by simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32790 p hg
    simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32792 (p : Pattern) (guard : d294933 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294932 p = 1 := by simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32791 p hg
    simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32793 (p : Pattern) (guard : d294934 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294933 p = 1 := by simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32792 p hg
    simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32794 (p : Pattern) (guard : d294935 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294934 p = 1 := by simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32793 p hg
    simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32795 (p : Pattern) (guard : d294936 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294929 p = 1 := by simpa only [d294936, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32789 p hg
    simpa only [d294936, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294935 p = 1 := by simpa only [d294936, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32794 p hg
    simpa only [d294936, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32796 (p : Pattern) (guard : d294937 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294930 p = 1 := by simpa only [d294937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32784 p hg
    simpa only [d294937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294936 p = 1 := by simpa only [d294937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32795 p hg
    simpa only [d294937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32797 (p : Pattern) (guard : d294938 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294924 p = 1 := by simpa only [d294938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32778 p hg
    simpa only [d294938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294937 p = 1 := by simpa only [d294938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32796 p hg
    simpa only [d294938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32798 (p : Pattern) (guard : d294939 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294938 p = 1 := by simpa only [d294939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32797 p hg
    simpa only [d294939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32799 (p : Pattern) (guard : d294940 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294852 p = 1 := by simpa only [d294940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32663 p hg
    simpa only [d294940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294939 p = 1 := by simpa only [d294940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32798 p hg
    simpa only [d294940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32800 (p : Pattern) (guard : d1532 p = 1) : d47706 p ≤ (1 : Int) + d47706 p := by
  omega
theorem compare32801 (p : Pattern) (guard : d25764 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32800 p hg
    simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32053 p hg
    simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32802 (p : Pattern) (guard : d25765 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32801 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32803 (p : Pattern) (guard : d25766 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32802 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32804 (p : Pattern) (guard : d31739 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32803 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32805 (p : Pattern) (guard : d294870 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32804 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32806 (p : Pattern) (guard : d294871 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32805 p hg
    simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32807 (p : Pattern) (guard : d294872 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32806 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32808 (p : Pattern) (guard : d294873 p = 1) : d49957 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32807 p hg
    simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32809 (p : Pattern) (guard : d294874 p = 1) : d49958 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294873 p = 1 := by simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32808 p hg
    simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32810 (p : Pattern) (guard : d294875 p = 1) : d49978 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294874 p = 1 := by simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32811 (p : Pattern) (guard : d294876 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294875 p = 1 := by simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32810 p hg
    simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32812 (p : Pattern) (guard : d294877 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294876 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32811 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32813 (p : Pattern) (guard : d294878 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294877 p = 1 := by simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32812 p hg
    simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32814 (p : Pattern) (guard : d293369 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32390 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32815 (p : Pattern) (guard : d293370 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32814 p hg
    simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32816 (p : Pattern) (guard : d293371 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32815 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32817 (p : Pattern) (guard : d293372 p = 1) : d49957 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32816 p hg
    simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32818 (p : Pattern) (guard : d293373 p = 1) : d49958 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293372 p = 1 := by simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32817 p hg
    simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32819 (p : Pattern) (guard : d293374 p = 1) : d49978 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293373 p = 1 := by simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32818 p hg
    simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32820 (p : Pattern) (guard : d293375 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293374 p = 1 := by simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32819 p hg
    simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32821 (p : Pattern) (guard : d294806 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293375 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32820 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32822 (p : Pattern) (guard : d294807 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294654 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32398 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294806 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32821 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32823 (p : Pattern) (guard : d294879 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294878 p = 1 := by simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32813 p hg
    simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294807 p = 1 := by simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32822 p hg
    simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32824 (p : Pattern) (guard : d294880 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294880, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d294880, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294879 p = 1 := by simpa only [d294880, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32823 p hg
    simpa only [d294880, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32825 (p : Pattern) (guard : d294881 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294881, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d294881, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294880 p = 1 := by simpa only [d294881, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32824 p hg
    simpa only [d294881, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32826 (p : Pattern) (guard : d293631 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293375 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32820 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32827 (p : Pattern) (guard : d294808 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294806 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32821 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293631 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32826 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32828 (p : Pattern) (guard : d294809 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294807 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32822 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294808 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32827 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32829 (p : Pattern) (guard : d294810 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294809 p = 1 := by simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32828 p hg
    simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32830 (p : Pattern) (guard : d294811 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294810 p = 1 := by simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32829 p hg
    simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32831 (p : Pattern) (guard : d294882 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294881 p = 1 := by simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32825 p hg
    simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294811 p = 1 := by simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32830 p hg
    simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32832 (p : Pattern) (guard : d294812 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293631 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32826 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32833 (p : Pattern) (guard : d294813 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294808 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32827 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294812 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32832 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32834 (p : Pattern) (guard : d294814 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294813 p = 1 := by simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32833 p hg
    simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32835 (p : Pattern) (guard : d294815 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294814 p = 1 := by simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32834 p hg
    simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32836 (p : Pattern) (guard : d294816 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294811 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32830 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294815 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32835 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32837 (p : Pattern) (guard : d294883 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294882 p = 1 := by simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32831 p hg
    simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294816 p = 1 := by simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32836 p hg
    simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32838 (p : Pattern) (guard : d294884 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294883 p = 1 := by simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32837 p hg
    simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32839 (p : Pattern) (guard : d294885 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294884 p = 1 := by simpa only [d294885, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32838 p hg
    simpa only [d294885, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294885, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d294885, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32840 (p : Pattern) (guard : d294886 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294886, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d294886, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294885 p = 1 := by simpa only [d294886, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32839 p hg
    simpa only [d294886, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32841 (p : Pattern) (guard : d294817 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294815 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32835 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32842 (p : Pattern) (guard : d294818 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294816 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32836 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294817 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32841 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32843 (p : Pattern) (guard : d294819 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294818 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32842 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32844 (p : Pattern) (guard : d294820 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294819 p = 1 := by simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32843 p hg
    simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32845 (p : Pattern) (guard : d294821 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294820 p = 1 := by simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32844 p hg
    simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32846 (p : Pattern) (guard : d294887 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294886 p = 1 := by simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32840 p hg
    simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294821 p = 1 := by simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32845 p hg
    simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32847 (p : Pattern) (guard : d294888 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294887 p = 1 := by simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32846 p hg
    simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32848 (p : Pattern) (guard : d294889 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294888 p = 1 := by simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32847 p hg
    simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32849 (p : Pattern) (guard : d294914 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294889 p = 1 := by simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32848 p hg
    simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32850 (p : Pattern) (guard : d294822 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294817 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32841 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32851 (p : Pattern) (guard : d294823 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294822 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32850 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32852 (p : Pattern) (guard : d294824 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294823 p = 1 := by simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32851 p hg
    simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32853 (p : Pattern) (guard : d294825 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294824 p = 1 := by simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32852 p hg
    simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32854 (p : Pattern) (guard : d294826 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32845 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294825 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32853 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32855 (p : Pattern) (guard : d294827 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294826 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32854 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32856 (p : Pattern) (guard : d294828 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294827 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32855 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32857 (p : Pattern) (guard : d294842 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294828 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32856 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32858 (p : Pattern) (guard : d294915 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294914 p = 1 := by simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32849 p hg
    simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294842 p = 1 := by simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32857 p hg
    simpa only [d294915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32859 (p : Pattern) (guard : d294916 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294915 p = 1 := by simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32858 p hg
    simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32860 (p : Pattern) (guard : d294893 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32845 p hg
    simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32861 (p : Pattern) (guard : d294894 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294893 p = 1 := by simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32860 p hg
    simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32862 (p : Pattern) (guard : d294895 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294894 p = 1 := by simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32861 p hg
    simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32863 (p : Pattern) (guard : d294917 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294895 p = 1 := by simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32862 p hg
    simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32864 (p : Pattern) (guard : d294918 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294917 p = 1 := by simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32863 p hg
    simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32865 (p : Pattern) (guard : d294919 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294918 p = 1 := by simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32864 p hg
    simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32866 (p : Pattern) (guard : d294920 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294916 p = 1 := by simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32859 p hg
    simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294919 p = 1 := by simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32865 p hg
    simpa only [d294920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32867 (p : Pattern) (guard : d294941 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294920 p = 1 := by simpa only [d294941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32866 p hg
    simpa only [d294941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32868 (p : Pattern) (guard : d294942 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294941 p = 1 := by simpa only [d294942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32867 p hg
    simpa only [d294942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32869 (p : Pattern) (guard : d294943 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294943, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294943, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294942 p = 1 := by simpa only [d294943, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32868 p hg
    simpa only [d294943, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32870 (p : Pattern) (guard : d294944 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294943 p = 1 := by simpa only [d294944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32869 p hg
    simpa only [d294944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32871 (p : Pattern) (guard : d294830 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294825 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32853 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32872 (p : Pattern) (guard : d294831 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294830 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32871 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32873 (p : Pattern) (guard : d294832 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294831 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32872 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32874 (p : Pattern) (guard : d294843 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294832 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32873 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32875 (p : Pattern) (guard : d294931 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294843 p = 1 := by simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32874 p hg
    simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32876 (p : Pattern) (guard : d294932 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294931 p = 1 := by simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32875 p hg
    simpa only [d294932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32877 (p : Pattern) (guard : d294933 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294932 p = 1 := by simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32876 p hg
    simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32878 (p : Pattern) (guard : d294934 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294933 p = 1 := by simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32877 p hg
    simpa only [d294934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32879 (p : Pattern) (guard : d294935 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294934 p = 1 := by simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32878 p hg
    simpa only [d294935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32880 (p : Pattern) (guard : d294945 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294945, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294945, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294935 p = 1 := by simpa only [d294945, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32879 p hg
    simpa only [d294945, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32881 (p : Pattern) (guard : d294946 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294945 p = 1 := by simpa only [d294946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32880 p hg
    simpa only [d294946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32882 (p : Pattern) (guard : d294947 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294944 p = 1 := by simpa only [d294947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32870 p hg
    simpa only [d294947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294946 p = 1 := by simpa only [d294947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32881 p hg
    simpa only [d294947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32883 (p : Pattern) (guard : d294948 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294947 p = 1 := by simpa only [d294948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32882 p hg
    simpa only [d294948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32884 (p : Pattern) (guard : d294949 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294948 p = 1 := by simpa only [d294949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32883 p hg
    simpa only [d294949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32885 (p : Pattern) (guard : d294950 p = 1) : d50002 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d294940 p = 1 := by simpa only [d294950, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32799 p hg
    simpa only [d294950, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294949 p = 1 := by simpa only [d294950, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32884 p hg
    simpa only [d294950, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32886 (p : Pattern) (guard : d1532 p = 1) : d47630 p ≤ (1 : Int) + d47630 p := by
  omega
theorem compare32887 (p : Pattern) (guard : d25764 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32886 p hg
    simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32105 p hg
    simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32888 (p : Pattern) (guard : d25765 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32887 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32889 (p : Pattern) (guard : d25766 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32888 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32890 (p : Pattern) (guard : d31739 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32891 (p : Pattern) (guard : d294870 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32890 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32892 (p : Pattern) (guard : d294871 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32891 p hg
    simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32893 (p : Pattern) (guard : d294872 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32892 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32894 (p : Pattern) (guard : d294951 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294872 p = 1 := by simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32893 p hg
    simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32895 (p : Pattern) (guard : d294873 p = 1) : d50030 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32688 p hg
    simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32896 (p : Pattern) (guard : d294952 p = 1) : d50031 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294951 p = 1 := by simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32894 p hg
    simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294873 p = 1 := by simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32895 p hg
    simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32897 (p : Pattern) (guard : d1532 p = 1) : d47634 p ≤ (1 : Int) + d47634 p := by
  omega
theorem compare32898 (p : Pattern) (guard : d25764 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32897 p hg
    simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32119 p hg
    simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32899 (p : Pattern) (guard : d25765 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32898 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32900 (p : Pattern) (guard : d25766 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32899 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32901 (p : Pattern) (guard : d31739 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32900 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32902 (p : Pattern) (guard : d294870 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32901 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32903 (p : Pattern) (guard : d294871 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32902 p hg
    simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32904 (p : Pattern) (guard : d294872 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32903 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32905 (p : Pattern) (guard : d294873 p = 1) : d49865 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32904 p hg
    simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32906 (p : Pattern) (guard : d294874 p = 1) : d49866 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294873 p = 1 := by simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32905 p hg
    simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32907 (p : Pattern) (guard : d294953 p = 1) : d50032 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294952 p = 1 := by simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32896 p hg
    simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294874 p = 1 := by simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32906 p hg
    simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32908 (p : Pattern) (guard : d294954 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294953 p = 1 := by simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32907 p hg
    simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32909 (p : Pattern) (guard : d294955 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294954 p = 1 := by simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32908 p hg
    simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32910 (p : Pattern) (guard : d294956 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294955 p = 1 := by simpa only [d294956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32909 p hg
    simpa only [d294956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32911 (p : Pattern) (guard : d293369 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32476 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32912 (p : Pattern) (guard : d293370 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32911 p hg
    simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32913 (p : Pattern) (guard : d293371 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32912 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32914 (p : Pattern) (guard : d293415 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293371 p = 1 := by simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32913 p hg
    simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32915 (p : Pattern) (guard : d293372 p = 1) : d50030 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32586 p hg
    simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32916 (p : Pattern) (guard : d293416 p = 1) : d50031 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293415 p = 1 := by simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32914 p hg
    simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293372 p = 1 := by simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32915 p hg
    simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32917 (p : Pattern) (guard : d293369 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32487 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32918 (p : Pattern) (guard : d293370 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32917 p hg
    simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32919 (p : Pattern) (guard : d293371 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32918 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32920 (p : Pattern) (guard : d293372 p = 1) : d49865 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32919 p hg
    simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32921 (p : Pattern) (guard : d293373 p = 1) : d49866 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293372 p = 1 := by simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32920 p hg
    simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32922 (p : Pattern) (guard : d293417 p = 1) : d50032 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d293416 p = 1 := by simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32916 p hg
    simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293373 p = 1 := by simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32921 p hg
    simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32923 (p : Pattern) (guard : d293418 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293417 p = 1 := by simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32922 p hg
    simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32924 (p : Pattern) (guard : d294957 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293418 p = 1 := by simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32923 p hg
    simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32925 (p : Pattern) (guard : d294958 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294732 p = 1 := by simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32495 p hg
    simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294957 p = 1 := by simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32924 p hg
    simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32926 (p : Pattern) (guard : d294959 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294956 p = 1 := by simpa only [d294959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32910 p hg
    simpa only [d294959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294958 p = 1 := by simpa only [d294959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32925 p hg
    simpa only [d294959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32927 (p : Pattern) (guard : d294960 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294960, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d294960, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294959 p = 1 := by simpa only [d294960, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32926 p hg
    simpa only [d294960, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32928 (p : Pattern) (guard : d294961 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294961, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d294961, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294960 p = 1 := by simpa only [d294961, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32927 p hg
    simpa only [d294961, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32929 (p : Pattern) (guard : d293813 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293418 p = 1 := by simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32923 p hg
    simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32930 (p : Pattern) (guard : d294962 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294957 p = 1 := by simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32924 p hg
    simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293813 p = 1 := by simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32929 p hg
    simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32931 (p : Pattern) (guard : d294963 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294958 p = 1 := by simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32925 p hg
    simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294962 p = 1 := by simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32930 p hg
    simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32932 (p : Pattern) (guard : d294964 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294963 p = 1 := by simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32931 p hg
    simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32933 (p : Pattern) (guard : d294965 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294964 p = 1 := by simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32932 p hg
    simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32934 (p : Pattern) (guard : d294966 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294961 p = 1 := by simpa only [d294966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32928 p hg
    simpa only [d294966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294965 p = 1 := by simpa only [d294966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32933 p hg
    simpa only [d294966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32935 (p : Pattern) (guard : d294967 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293813 p = 1 := by simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32929 p hg
    simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32936 (p : Pattern) (guard : d294968 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294962 p = 1 := by simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32930 p hg
    simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294967 p = 1 := by simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32935 p hg
    simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32937 (p : Pattern) (guard : d294969 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294968 p = 1 := by simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32936 p hg
    simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32938 (p : Pattern) (guard : d294970 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294969 p = 1 := by simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32937 p hg
    simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32939 (p : Pattern) (guard : d294971 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294965 p = 1 := by simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32933 p hg
    simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294970 p = 1 := by simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32938 p hg
    simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32940 (p : Pattern) (guard : d294972 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294966 p = 1 := by simpa only [d294972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32934 p hg
    simpa only [d294972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294971 p = 1 := by simpa only [d294972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32939 p hg
    simpa only [d294972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32941 (p : Pattern) (guard : d294973 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294972 p = 1 := by simpa only [d294973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32940 p hg
    simpa only [d294973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32942 (p : Pattern) (guard : d294974 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294973 p = 1 := by simpa only [d294974, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32941 p hg
    simpa only [d294974, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294974, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d294974, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32943 (p : Pattern) (guard : d294975 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294975, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294975, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294974 p = 1 := by simpa only [d294975, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32942 p hg
    simpa only [d294975, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32944 (p : Pattern) (guard : d294976 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294970 p = 1 := by simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32938 p hg
    simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32945 (p : Pattern) (guard : d294977 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294971 p = 1 := by simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32939 p hg
    simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294976 p = 1 := by simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32944 p hg
    simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32946 (p : Pattern) (guard : d294978 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294977 p = 1 := by simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32945 p hg
    simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32947 (p : Pattern) (guard : d294979 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294978 p = 1 := by simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32946 p hg
    simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32948 (p : Pattern) (guard : d294980 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294979 p = 1 := by simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32947 p hg
    simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32949 (p : Pattern) (guard : d294981 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294975 p = 1 := by simpa only [d294981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32943 p hg
    simpa only [d294981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294980 p = 1 := by simpa only [d294981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32948 p hg
    simpa only [d294981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32950 (p : Pattern) (guard : d294982 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294981 p = 1 := by simpa only [d294982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32949 p hg
    simpa only [d294982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32951 (p : Pattern) (guard : d294983 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294982 p = 1 := by simpa only [d294983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32950 p hg
    simpa only [d294983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32952 (p : Pattern) (guard : d294984 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294983 p = 1 := by simpa only [d294984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32951 p hg
    simpa only [d294984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32953 (p : Pattern) (guard : d294985 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294976 p = 1 := by simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32944 p hg
    simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32954 (p : Pattern) (guard : d294986 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294985 p = 1 := by simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32953 p hg
    simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32955 (p : Pattern) (guard : d294987 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294986 p = 1 := by simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32954 p hg
    simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32956 (p : Pattern) (guard : d294988 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294987 p = 1 := by simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32955 p hg
    simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32957 (p : Pattern) (guard : d294989 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294980 p = 1 := by simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32948 p hg
    simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294988 p = 1 := by simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32956 p hg
    simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32958 (p : Pattern) (guard : d294990 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294989 p = 1 := by simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32957 p hg
    simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32959 (p : Pattern) (guard : d294991 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294990 p = 1 := by simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32958 p hg
    simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32960 (p : Pattern) (guard : d294992 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294991 p = 1 := by simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32959 p hg
    simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32961 (p : Pattern) (guard : d294993 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294984 p = 1 := by simpa only [d294993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32952 p hg
    simpa only [d294993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294992 p = 1 := by simpa only [d294993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32960 p hg
    simpa only [d294993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32962 (p : Pattern) (guard : d294994 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294993 p = 1 := by simpa only [d294994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32961 p hg
    simpa only [d294994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32963 (p : Pattern) (guard : d294995 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294980 p = 1 := by simpa only [d294995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32948 p hg
    simpa only [d294995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32964 (p : Pattern) (guard : d294996 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294995 p = 1 := by simpa only [d294996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32963 p hg
    simpa only [d294996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32965 (p : Pattern) (guard : d294997 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294996 p = 1 := by simpa only [d294997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32964 p hg
    simpa only [d294997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32966 (p : Pattern) (guard : d294998 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294997 p = 1 := by simpa only [d294998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32965 p hg
    simpa only [d294998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32967 (p : Pattern) (guard : d294999 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294998 p = 1 := by simpa only [d294999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32966 p hg
    simpa only [d294999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32968 (p : Pattern) (guard : d295000 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294999 p = 1 := by simpa only [d295000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32967 p hg
    simpa only [d295000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32969 (p : Pattern) (guard : d295001 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294994 p = 1 := by simpa only [d295001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32962 p hg
    simpa only [d295001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295000 p = 1 := by simpa only [d295001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32968 p hg
    simpa only [d295001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32970 (p : Pattern) (guard : d295002 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295001 p = 1 := by simpa only [d295002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32969 p hg
    simpa only [d295002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32971 (p : Pattern) (guard : d295003 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295002 p = 1 := by simpa only [d295003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32970 p hg
    simpa only [d295003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32972 (p : Pattern) (guard : d295004 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295004, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295004, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295003 p = 1 := by simpa only [d295004, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32971 p hg
    simpa only [d295004, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32973 (p : Pattern) (guard : d295005 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295004 p = 1 := by simpa only [d295005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32972 p hg
    simpa only [d295005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32974 (p : Pattern) (guard : d295006 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294988 p = 1 := by simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32956 p hg
    simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32975 (p : Pattern) (guard : d295007 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295006 p = 1 := by simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32974 p hg
    simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32976 (p : Pattern) (guard : d295008 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295007 p = 1 := by simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32975 p hg
    simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32977 (p : Pattern) (guard : d295009 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295008 p = 1 := by simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32976 p hg
    simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32978 (p : Pattern) (guard : d295010 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295009 p = 1 := by simpa only [d295010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32977 p hg
    simpa only [d295010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32979 (p : Pattern) (guard : d295011 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295010 p = 1 := by simpa only [d295011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32978 p hg
    simpa only [d295011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32980 (p : Pattern) (guard : d295012 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295011 p = 1 := by simpa only [d295012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32979 p hg
    simpa only [d295012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32981 (p : Pattern) (guard : d295013 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295012 p = 1 := by simpa only [d295013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32980 p hg
    simpa only [d295013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32982 (p : Pattern) (guard : d295014 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295013 p = 1 := by simpa only [d295014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32981 p hg
    simpa only [d295014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32983 (p : Pattern) (guard : d295015 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295015, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295015, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295014 p = 1 := by simpa only [d295015, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32982 p hg
    simpa only [d295015, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32984 (p : Pattern) (guard : d295016 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295015 p = 1 := by simpa only [d295016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32983 p hg
    simpa only [d295016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32985 (p : Pattern) (guard : d295017 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295005 p = 1 := by simpa only [d295017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32973 p hg
    simpa only [d295017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295016 p = 1 := by simpa only [d295017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32984 p hg
    simpa only [d295017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32986 (p : Pattern) (guard : d295018 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295017 p = 1 := by simpa only [d295018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32985 p hg
    simpa only [d295018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32987 (p : Pattern) (guard : d295019 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295018 p = 1 := by simpa only [d295019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32986 p hg
    simpa only [d295019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32988 (p : Pattern) (guard : d295020 p = 1) : d50100 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295019 p = 1 := by simpa only [d295020, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32987 p hg
    simpa only [d295020, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295020, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32160 p hg
    simpa only [d295020, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32989 (p : Pattern) (guard : d295021 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d294950 p = 1 := by simpa only [d295021, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32885 p hg
    simpa only [d295021, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295020 p = 1 := by simpa only [d295021, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32988 p hg
    simpa only [d295021, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32990 (p : Pattern) (guard : d295022 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295021 p = 1 := by simpa only [d295022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32989 p hg
    simpa only [d295022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32991 (p : Pattern) (guard : d295023 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295022 p = 1 := by simpa only [d295023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32990 p hg
    simpa only [d295023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32992 (p : Pattern) (guard : d295024 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295023 p = 1 := by simpa only [d295024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32991 p hg
    simpa only [d295024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32993 (p : Pattern) (guard : d295025 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295024 p = 1 := by simpa only [d295025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32992 p hg
    simpa only [d295025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32994 (p : Pattern) (guard : d295026 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295025 p = 1 := by simpa only [d295026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32993 p hg
    simpa only [d295026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32995 (p : Pattern) (guard : d295027 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295026 p = 1 := by simpa only [d295027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32994 p hg
    simpa only [d295027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32996 (p : Pattern) (guard : d295028 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295027 p = 1 := by simpa only [d295028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32995 p hg
    simpa only [d295028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32997 (p : Pattern) (guard : d295029 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295028 p = 1 := by simpa only [d295029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32996 p hg
    simpa only [d295029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32998 (p : Pattern) (guard : d295030 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d294805 p = 1 := by simpa only [d295030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32583 p hg
    simpa only [d295030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295029 p = 1 := by simpa only [d295030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32997 p hg
    simpa only [d295030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32999 (p : Pattern) (guard : d293903 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32685 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
