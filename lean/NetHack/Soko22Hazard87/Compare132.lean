import NetHack.Soko22Hazard87.Compare131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33000 (p : Pattern) (guard : d293904 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32999 p hg
    simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33001 (p : Pattern) (guard : d293905 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33000 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33002 (p : Pattern) (guard : d293906 p = 1) : d49838 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33001 p hg
    simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33003 (p : Pattern) (guard : d293907 p = 1) : d49841 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293906 p = 1 := by simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33002 p hg
    simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33004 (p : Pattern) (guard : d293908 p = 1) : d49864 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293907 p = 1 := by simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33003 p hg
    simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33005 (p : Pattern) (guard : d293909 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293908 p = 1 := by simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33004 p hg
    simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33006 (p : Pattern) (guard : d295031 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293909 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33005 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33007 (p : Pattern) (guard : d295032 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294877 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32693 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295031 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33006 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33008 (p : Pattern) (guard : d293921 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293909 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33005 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33009 (p : Pattern) (guard : d295033 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295031 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33006 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293921 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33008 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33010 (p : Pattern) (guard : d295034 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295032 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33007 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295033 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33009 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33011 (p : Pattern) (guard : d295035 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295034 p = 1 := by simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33010 p hg
    simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33012 (p : Pattern) (guard : d295036 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295035 p = 1 := by simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33011 p hg
    simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33013 (p : Pattern) (guard : d295037 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293921 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33008 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33014 (p : Pattern) (guard : d295038 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295033 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33009 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295037 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33013 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33015 (p : Pattern) (guard : d295039 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295038 p = 1 := by simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33014 p hg
    simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33016 (p : Pattern) (guard : d295040 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295039 p = 1 := by simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33015 p hg
    simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33017 (p : Pattern) (guard : d295041 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295036 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33012 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295040 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33016 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33018 (p : Pattern) (guard : d295042 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295040 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33016 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33019 (p : Pattern) (guard : d295043 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295041 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33017 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295042 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33018 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33020 (p : Pattern) (guard : d295044 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295043 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33019 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33021 (p : Pattern) (guard : d295045 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295044 p = 1 := by simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33020 p hg
    simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33022 (p : Pattern) (guard : d295046 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295045 p = 1 := by simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33021 p hg
    simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33023 (p : Pattern) (guard : d295047 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295042 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33018 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33024 (p : Pattern) (guard : d295048 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295047 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33023 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33025 (p : Pattern) (guard : d295049 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295048 p = 1 := by simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33024 p hg
    simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33026 (p : Pattern) (guard : d295050 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295049 p = 1 := by simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33025 p hg
    simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33027 (p : Pattern) (guard : d295051 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33022 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295050 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33026 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33028 (p : Pattern) (guard : d295052 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295051 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33027 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33029 (p : Pattern) (guard : d295053 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295052 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33028 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33030 (p : Pattern) (guard : d295054 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295053 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33029 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33031 (p : Pattern) (guard : d295055 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295050 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33026 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33032 (p : Pattern) (guard : d295056 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295055 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33033 (p : Pattern) (guard : d295057 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295056 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33032 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33034 (p : Pattern) (guard : d295058 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295057 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33033 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33035 (p : Pattern) (guard : d295059 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295054 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33030 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295058 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33034 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33036 (p : Pattern) (guard : d295060 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295059 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33035 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33037 (p : Pattern) (guard : d295061 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295060 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33036 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33038 (p : Pattern) (guard : d295062 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295061 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33037 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33039 (p : Pattern) (guard : d295063 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295062 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33038 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33040 (p : Pattern) (guard : d295064 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295063 p = 1 := by simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33039 p hg
    simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33041 (p : Pattern) (guard : d295065 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295064 p = 1 := by simpa only [d295065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33040 p hg
    simpa only [d295065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33042 (p : Pattern) (guard : d295066 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295065 p = 1 := by simpa only [d295066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33041 p hg
    simpa only [d295066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33043 (p : Pattern) (guard : d295036 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295035 p = 1 := by simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33011 p hg
    simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33044 (p : Pattern) (guard : d295040 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295039 p = 1 := by simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33015 p hg
    simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33045 (p : Pattern) (guard : d295041 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295036 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33043 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295040 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33044 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33046 (p : Pattern) (guard : d295042 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295040 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33044 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33047 (p : Pattern) (guard : d295043 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295041 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33045 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295042 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33046 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33048 (p : Pattern) (guard : d295044 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295043 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33047 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33049 (p : Pattern) (guard : d295045 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295044 p = 1 := by simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33048 p hg
    simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33050 (p : Pattern) (guard : d295046 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295045 p = 1 := by simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33049 p hg
    simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33051 (p : Pattern) (guard : d295047 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295042 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33046 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33052 (p : Pattern) (guard : d295048 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295047 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33051 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33053 (p : Pattern) (guard : d295049 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295048 p = 1 := by simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33052 p hg
    simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33054 (p : Pattern) (guard : d295050 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295049 p = 1 := by simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33053 p hg
    simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33055 (p : Pattern) (guard : d295051 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33050 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295050 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33054 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33056 (p : Pattern) (guard : d295052 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295051 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33055 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33057 (p : Pattern) (guard : d295053 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295052 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33056 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33058 (p : Pattern) (guard : d295054 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295053 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33057 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33059 (p : Pattern) (guard : d295055 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295050 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33054 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33060 (p : Pattern) (guard : d295056 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295055 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33059 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33061 (p : Pattern) (guard : d295057 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295056 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33060 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33062 (p : Pattern) (guard : d295058 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295057 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33061 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33063 (p : Pattern) (guard : d295059 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295054 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33058 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295058 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33062 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33064 (p : Pattern) (guard : d295060 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295059 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33063 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33065 (p : Pattern) (guard : d295061 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295060 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33064 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33066 (p : Pattern) (guard : d295062 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295061 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33065 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33067 (p : Pattern) (guard : d295063 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295062 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33066 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33068 (p : Pattern) (guard : d295067 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295053 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33029 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33069 (p : Pattern) (guard : d295068 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295057 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33033 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33070 (p : Pattern) (guard : d295069 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295067 p = 1 := by simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33068 p hg
    simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295068 p = 1 := by simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33069 p hg
    simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33071 (p : Pattern) (guard : d295070 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295069 p = 1 := by simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33070 p hg
    simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33072 (p : Pattern) (guard : d295071 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295070 p = 1 := by simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33071 p hg
    simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33073 (p : Pattern) (guard : d295072 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295071 p = 1 := by simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33072 p hg
    simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33074 (p : Pattern) (guard : d295073 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295072 p = 1 := by simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33073 p hg
    simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33075 (p : Pattern) (guard : d295074 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295063 p = 1 := by simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33067 p hg
    simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295073 p = 1 := by simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33074 p hg
    simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33076 (p : Pattern) (guard : d295075 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295064 p = 1 := by simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33040 p hg
    simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295074 p = 1 := by simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33075 p hg
    simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33077 (p : Pattern) (guard : d295076 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295075 p = 1 := by simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33076 p hg
    simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33078 (p : Pattern) (guard : d295077 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295066 p = 1 := by simpa only [d295077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33042 p hg
    simpa only [d295077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295076 p = 1 := by simpa only [d295077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33077 p hg
    simpa only [d295077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33079 (p : Pattern) (guard : d295078 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295052 p = 1 := by simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33028 p hg
    simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33080 (p : Pattern) (guard : d295079 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295078 p = 1 := by simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33079 p hg
    simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33081 (p : Pattern) (guard : d295080 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295056 p = 1 := by simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33032 p hg
    simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33082 (p : Pattern) (guard : d295081 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295080 p = 1 := by simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33081 p hg
    simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33083 (p : Pattern) (guard : d295082 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295079 p = 1 := by simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33080 p hg
    simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295081 p = 1 := by simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33082 p hg
    simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33084 (p : Pattern) (guard : d295083 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295082 p = 1 := by simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33083 p hg
    simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33085 (p : Pattern) (guard : d295084 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295083 p = 1 := by simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33084 p hg
    simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33086 (p : Pattern) (guard : d295085 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295084 p = 1 := by simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33085 p hg
    simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33087 (p : Pattern) (guard : d295086 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295051 p = 1 := by simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33027 p hg
    simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33088 (p : Pattern) (guard : d295087 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295086 p = 1 := by simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33087 p hg
    simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33089 (p : Pattern) (guard : d295088 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295087 p = 1 := by simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33088 p hg
    simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33090 (p : Pattern) (guard : d295089 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295055 p = 1 := by simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33091 (p : Pattern) (guard : d295090 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295089 p = 1 := by simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33090 p hg
    simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33092 (p : Pattern) (guard : d295091 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295090 p = 1 := by simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33091 p hg
    simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33093 (p : Pattern) (guard : d295092 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295088 p = 1 := by simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33089 p hg
    simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295091 p = 1 := by simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33092 p hg
    simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33094 (p : Pattern) (guard : d295093 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295092 p = 1 := by simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33093 p hg
    simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33095 (p : Pattern) (guard : d295094 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295093 p = 1 := by simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33094 p hg
    simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33096 (p : Pattern) (guard : d295095 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295032 p = 1 := by simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33007 p hg
    simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33097 (p : Pattern) (guard : d295096 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295096, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d295096, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295095 p = 1 := by simpa only [d295096, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33096 p hg
    simpa only [d295096, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33098 (p : Pattern) (guard : d295097 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295097, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d295097, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295096 p = 1 := by simpa only [d295097, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33097 p hg
    simpa only [d295097, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33099 (p : Pattern) (guard : d295098 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295097 p = 1 := by simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33098 p hg
    simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295036 p = 1 := by simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33012 p hg
    simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33100 (p : Pattern) (guard : d295099 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295098 p = 1 := by simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33099 p hg
    simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295041 p = 1 := by simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33017 p hg
    simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33101 (p : Pattern) (guard : d295100 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295099 p = 1 := by simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33100 p hg
    simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33102 (p : Pattern) (guard : d295101 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295100 p = 1 := by simpa only [d295101, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33101 p hg
    simpa only [d295101, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295101, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295101, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33103 (p : Pattern) (guard : d295102 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295102, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295102, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295101 p = 1 := by simpa only [d295102, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33102 p hg
    simpa only [d295102, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33104 (p : Pattern) (guard : d295103 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295102 p = 1 := by simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33103 p hg
    simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295046 p = 1 := by simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33022 p hg
    simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33105 (p : Pattern) (guard : d295104 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295103 p = 1 := by simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33104 p hg
    simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33106 (p : Pattern) (guard : d295105 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295104 p = 1 := by simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33105 p hg
    simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33107 (p : Pattern) (guard : d295106 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295105 p = 1 := by simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33106 p hg
    simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33108 (p : Pattern) (guard : d295107 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295106 p = 1 := by simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33107 p hg
    simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295054 p = 1 := by simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33030 p hg
    simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33109 (p : Pattern) (guard : d295108 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295107 p = 1 := by simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33108 p hg
    simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33110 (p : Pattern) (guard : d295109 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33022 p hg
    simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33111 (p : Pattern) (guard : d295110 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295109 p = 1 := by simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33110 p hg
    simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33112 (p : Pattern) (guard : d295111 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295110 p = 1 := by simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33111 p hg
    simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33113 (p : Pattern) (guard : d295112 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295111 p = 1 := by simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33112 p hg
    simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33114 (p : Pattern) (guard : d295113 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295112 p = 1 := by simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33113 p hg
    simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33115 (p : Pattern) (guard : d295114 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295113 p = 1 := by simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33114 p hg
    simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33116 (p : Pattern) (guard : d295115 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295108 p = 1 := by simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33109 p hg
    simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295114 p = 1 := by simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33115 p hg
    simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33117 (p : Pattern) (guard : d295116 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d295094 p = 1 := by simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33095 p hg
    simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295115 p = 1 := by simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33116 p hg
    simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33118 (p : Pattern) (guard : d295117 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d295085 p = 1 := by simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33086 p hg
    simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295116 p = 1 := by simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33117 p hg
    simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33119 (p : Pattern) (guard : d295118 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295118, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295118, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295117 p = 1 := by simpa only [d295118, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33118 p hg
    simpa only [d295118, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33120 (p : Pattern) (guard : d295078 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295052 p = 1 := by simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33056 p hg
    simpa only [d295078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33121 (p : Pattern) (guard : d295079 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295078 p = 1 := by simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33120 p hg
    simpa only [d295079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33122 (p : Pattern) (guard : d295080 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295056 p = 1 := by simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33060 p hg
    simpa only [d295080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33123 (p : Pattern) (guard : d295081 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295080 p = 1 := by simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33122 p hg
    simpa only [d295081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33124 (p : Pattern) (guard : d295082 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295079 p = 1 := by simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33121 p hg
    simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295081 p = 1 := by simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33123 p hg
    simpa only [d295082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33125 (p : Pattern) (guard : d295083 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295082 p = 1 := by simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33124 p hg
    simpa only [d295083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33126 (p : Pattern) (guard : d295084 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295083 p = 1 := by simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33125 p hg
    simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33127 (p : Pattern) (guard : d295085 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295084 p = 1 := by simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33126 p hg
    simpa only [d295085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33128 (p : Pattern) (guard : d295086 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295051 p = 1 := by simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33055 p hg
    simpa only [d295086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33129 (p : Pattern) (guard : d295087 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295086 p = 1 := by simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33128 p hg
    simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33130 (p : Pattern) (guard : d295088 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295087 p = 1 := by simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33129 p hg
    simpa only [d295088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33131 (p : Pattern) (guard : d295089 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295055 p = 1 := by simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33059 p hg
    simpa only [d295089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33132 (p : Pattern) (guard : d295090 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295089 p = 1 := by simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33131 p hg
    simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33133 (p : Pattern) (guard : d295091 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295090 p = 1 := by simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33132 p hg
    simpa only [d295091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33134 (p : Pattern) (guard : d295092 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295088 p = 1 := by simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33130 p hg
    simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295091 p = 1 := by simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33133 p hg
    simpa only [d295092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33135 (p : Pattern) (guard : d295093 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295092 p = 1 := by simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33134 p hg
    simpa only [d295093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33136 (p : Pattern) (guard : d295094 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295093 p = 1 := by simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33135 p hg
    simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33137 (p : Pattern) (guard : d295097 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295097, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d295097, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295096 p = 1 := by simpa only [d295097, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33097 p hg
    simpa only [d295097, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33138 (p : Pattern) (guard : d295098 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295097 p = 1 := by simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33137 p hg
    simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295036 p = 1 := by simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33043 p hg
    simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33139 (p : Pattern) (guard : d295099 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295098 p = 1 := by simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33138 p hg
    simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295041 p = 1 := by simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33045 p hg
    simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33140 (p : Pattern) (guard : d295100 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295099 p = 1 := by simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33139 p hg
    simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33141 (p : Pattern) (guard : d295101 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295100 p = 1 := by simpa only [d295101, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33140 p hg
    simpa only [d295101, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295101, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295101, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33142 (p : Pattern) (guard : d295102 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295102, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d295102, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295101 p = 1 := by simpa only [d295102, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33141 p hg
    simpa only [d295102, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33143 (p : Pattern) (guard : d295103 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295102 p = 1 := by simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33142 p hg
    simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295046 p = 1 := by simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33050 p hg
    simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33144 (p : Pattern) (guard : d295104 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295103 p = 1 := by simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33143 p hg
    simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33145 (p : Pattern) (guard : d295105 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295104 p = 1 := by simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33144 p hg
    simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33146 (p : Pattern) (guard : d295106 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295105 p = 1 := by simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33145 p hg
    simpa only [d295106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33147 (p : Pattern) (guard : d295107 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295106 p = 1 := by simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33146 p hg
    simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295054 p = 1 := by simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33058 p hg
    simpa only [d295107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33148 (p : Pattern) (guard : d295108 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295107 p = 1 := by simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33147 p hg
    simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33149 (p : Pattern) (guard : d295109 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33050 p hg
    simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33150 (p : Pattern) (guard : d295110 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295109 p = 1 := by simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33149 p hg
    simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33151 (p : Pattern) (guard : d295111 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295110 p = 1 := by simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33150 p hg
    simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33152 (p : Pattern) (guard : d295112 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295111 p = 1 := by simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33151 p hg
    simpa only [d295112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33153 (p : Pattern) (guard : d295113 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295112 p = 1 := by simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33152 p hg
    simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33154 (p : Pattern) (guard : d295114 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295113 p = 1 := by simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33153 p hg
    simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33155 (p : Pattern) (guard : d295115 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295108 p = 1 := by simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33148 p hg
    simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295114 p = 1 := by simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33154 p hg
    simpa only [d295115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33156 (p : Pattern) (guard : d295116 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d295094 p = 1 := by simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33136 p hg
    simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295115 p = 1 := by simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33155 p hg
    simpa only [d295116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33157 (p : Pattern) (guard : d295117 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d295085 p = 1 := by simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33127 p hg
    simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295116 p = 1 := by simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33156 p hg
    simpa only [d295117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33158 (p : Pattern) (guard : d295119 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295078 p = 1 := by simpa only [d295119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33079 p hg
    simpa only [d295119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33159 (p : Pattern) (guard : d295120 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295080 p = 1 := by simpa only [d295120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33081 p hg
    simpa only [d295120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33160 (p : Pattern) (guard : d295121 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295119 p = 1 := by simpa only [d295121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33158 p hg
    simpa only [d295121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295120 p = 1 := by simpa only [d295121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33159 p hg
    simpa only [d295121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33161 (p : Pattern) (guard : d295122 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295121 p = 1 := by simpa only [d295122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33160 p hg
    simpa only [d295122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33162 (p : Pattern) (guard : d295123 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295122 p = 1 := by simpa only [d295123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33161 p hg
    simpa only [d295123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33163 (p : Pattern) (guard : d295124 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295123 p = 1 := by simpa only [d295124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33162 p hg
    simpa only [d295124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33164 (p : Pattern) (guard : d295125 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295087 p = 1 := by simpa only [d295125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33088 p hg
    simpa only [d295125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33165 (p : Pattern) (guard : d295126 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295090 p = 1 := by simpa only [d295126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33091 p hg
    simpa only [d295126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33166 (p : Pattern) (guard : d295127 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295125 p = 1 := by simpa only [d295127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33164 p hg
    simpa only [d295127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295126 p = 1 := by simpa only [d295127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33165 p hg
    simpa only [d295127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33167 (p : Pattern) (guard : d295128 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295127 p = 1 := by simpa only [d295128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33166 p hg
    simpa only [d295128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33168 (p : Pattern) (guard : d295129 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295128 p = 1 := by simpa only [d295129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33167 p hg
    simpa only [d295129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33169 (p : Pattern) (guard : d295130 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295105 p = 1 := by simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33106 p hg
    simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33170 (p : Pattern) (guard : d295131 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295130 p = 1 := by simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33169 p hg
    simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295067 p = 1 := by simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33068 p hg
    simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33171 (p : Pattern) (guard : d295132 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295131 p = 1 := by simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33170 p hg
    simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33172 (p : Pattern) (guard : d295133 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295111 p = 1 := by simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33112 p hg
    simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33173 (p : Pattern) (guard : d295134 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295133 p = 1 := by simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33172 p hg
    simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33174 (p : Pattern) (guard : d295135 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295134 p = 1 := by simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33173 p hg
    simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33175 (p : Pattern) (guard : d295136 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295132 p = 1 := by simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33171 p hg
    simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295135 p = 1 := by simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33174 p hg
    simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33176 (p : Pattern) (guard : d295137 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d295129 p = 1 := by simpa only [d295137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33168 p hg
    simpa only [d295137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295136 p = 1 := by simpa only [d295137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33175 p hg
    simpa only [d295137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33177 (p : Pattern) (guard : d295138 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d295124 p = 1 := by simpa only [d295138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33163 p hg
    simpa only [d295138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295137 p = 1 := by simpa only [d295138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33176 p hg
    simpa only [d295138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33178 (p : Pattern) (guard : d295139 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295117 p = 1 := by simpa only [d295139, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33157 p hg
    simpa only [d295139, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295138 p = 1 := by simpa only [d295139, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33177 p hg
    simpa only [d295139, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33179 (p : Pattern) (guard : d295140 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295118 p = 1 := by simpa only [d295140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33119 p hg
    simpa only [d295140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295139 p = 1 := by simpa only [d295140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33178 p hg
    simpa only [d295140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33180 (p : Pattern) (guard : d295141 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295058 p = 1 := by simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33034 p hg
    simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33181 (p : Pattern) (guard : d295142 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295141 p = 1 := by simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33180 p hg
    simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33182 (p : Pattern) (guard : d295143 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295142 p = 1 := by simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33181 p hg
    simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33183 (p : Pattern) (guard : d295144 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295143 p = 1 := by simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33182 p hg
    simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33184 (p : Pattern) (guard : d295145 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295144 p = 1 := by simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33183 p hg
    simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33185 (p : Pattern) (guard : d295146 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295063 p = 1 := by simpa only [d295146, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33067 p hg
    simpa only [d295146, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295145 p = 1 := by simpa only [d295146, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33184 p hg
    simpa only [d295146, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33186 (p : Pattern) (guard : d295141 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295058 p = 1 := by simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33062 p hg
    simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33187 (p : Pattern) (guard : d295142 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295141 p = 1 := by simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33186 p hg
    simpa only [d295142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33188 (p : Pattern) (guard : d295143 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295142 p = 1 := by simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33187 p hg
    simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33189 (p : Pattern) (guard : d295144 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295143 p = 1 := by simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33188 p hg
    simpa only [d295144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33190 (p : Pattern) (guard : d295145 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295144 p = 1 := by simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33189 p hg
    simpa only [d295145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33191 (p : Pattern) (guard : d295147 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295068 p = 1 := by simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33069 p hg
    simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33192 (p : Pattern) (guard : d295148 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295147 p = 1 := by simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33191 p hg
    simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33193 (p : Pattern) (guard : d295149 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295148 p = 1 := by simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33192 p hg
    simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33194 (p : Pattern) (guard : d295150 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295149 p = 1 := by simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33193 p hg
    simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33195 (p : Pattern) (guard : d295151 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295150 p = 1 := by simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33194 p hg
    simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33196 (p : Pattern) (guard : d295152 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295145 p = 1 := by simpa only [d295152, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33190 p hg
    simpa only [d295152, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295151 p = 1 := by simpa only [d295152, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33195 p hg
    simpa only [d295152, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33197 (p : Pattern) (guard : d295153 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295146 p = 1 := by simpa only [d295153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33185 p hg
    simpa only [d295153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295152 p = 1 := by simpa only [d295153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33196 p hg
    simpa only [d295153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33198 (p : Pattern) (guard : d295154 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295140 p = 1 := by simpa only [d295154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33179 p hg
    simpa only [d295154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295153 p = 1 := by simpa only [d295154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33197 p hg
    simpa only [d295154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33199 (p : Pattern) (guard : d295155 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295154 p = 1 := by simpa only [d295155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33198 p hg
    simpa only [d295155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33200 (p : Pattern) (guard : d295156 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295077 p = 1 := by simpa only [d295156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33078 p hg
    simpa only [d295156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295155 p = 1 := by simpa only [d295156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33199 p hg
    simpa only [d295156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33201 (p : Pattern) (guard : d293903 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32804 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33202 (p : Pattern) (guard : d293904 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33201 p hg
    simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33203 (p : Pattern) (guard : d293905 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33202 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33204 (p : Pattern) (guard : d293906 p = 1) : d49957 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33203 p hg
    simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33205 (p : Pattern) (guard : d293907 p = 1) : d49958 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293906 p = 1 := by simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33204 p hg
    simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33206 (p : Pattern) (guard : d293908 p = 1) : d49978 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293907 p = 1 := by simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33205 p hg
    simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33207 (p : Pattern) (guard : d293909 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293908 p = 1 := by simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33206 p hg
    simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33208 (p : Pattern) (guard : d295031 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293909 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33207 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33209 (p : Pattern) (guard : d295032 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294877 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32812 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295031 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33208 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33210 (p : Pattern) (guard : d295095 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295032 p = 1 := by simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33209 p hg
    simpa only [d295095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33211 (p : Pattern) (guard : d295096 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295096, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d295096, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295095 p = 1 := by simpa only [d295096, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33210 p hg
    simpa only [d295096, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33212 (p : Pattern) (guard : d295097 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295097, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d295097, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295096 p = 1 := by simpa only [d295097, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33211 p hg
    simpa only [d295097, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33213 (p : Pattern) (guard : d293921 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293909 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33207 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33214 (p : Pattern) (guard : d295033 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295031 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33208 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293921 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33213 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33215 (p : Pattern) (guard : d295034 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295032 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33209 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295033 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33214 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33216 (p : Pattern) (guard : d295035 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295034 p = 1 := by simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33215 p hg
    simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33217 (p : Pattern) (guard : d295036 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295035 p = 1 := by simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33216 p hg
    simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33218 (p : Pattern) (guard : d295098 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295097 p = 1 := by simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33212 p hg
    simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295036 p = 1 := by simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33217 p hg
    simpa only [d295098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33219 (p : Pattern) (guard : d295037 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293921 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33213 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33220 (p : Pattern) (guard : d295038 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295033 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33214 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295037 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33219 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33221 (p : Pattern) (guard : d295039 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295038 p = 1 := by simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33220 p hg
    simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33222 (p : Pattern) (guard : d295040 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295039 p = 1 := by simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33221 p hg
    simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33223 (p : Pattern) (guard : d295041 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295036 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33217 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295040 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33222 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33224 (p : Pattern) (guard : d295099 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295098 p = 1 := by simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33218 p hg
    simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295041 p = 1 := by simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33223 p hg
    simpa only [d295099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33225 (p : Pattern) (guard : d295100 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295099 p = 1 := by simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33224 p hg
    simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33226 (p : Pattern) (guard : d295101 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295100 p = 1 := by simpa only [d295101, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33225 p hg
    simpa only [d295101, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295101, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d295101, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33227 (p : Pattern) (guard : d295102 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295102, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d295102, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295101 p = 1 := by simpa only [d295102, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33226 p hg
    simpa only [d295102, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33228 (p : Pattern) (guard : d295042 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295040 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33222 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33229 (p : Pattern) (guard : d295043 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295041 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33223 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295042 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33228 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33230 (p : Pattern) (guard : d295044 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295043 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33229 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33231 (p : Pattern) (guard : d295045 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295044 p = 1 := by simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33230 p hg
    simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33232 (p : Pattern) (guard : d295046 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295045 p = 1 := by simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33231 p hg
    simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33233 (p : Pattern) (guard : d295103 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295102 p = 1 := by simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33227 p hg
    simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295046 p = 1 := by simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33232 p hg
    simpa only [d295103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33234 (p : Pattern) (guard : d295104 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295103 p = 1 := by simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33233 p hg
    simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33235 (p : Pattern) (guard : d295105 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295104 p = 1 := by simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33234 p hg
    simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33236 (p : Pattern) (guard : d295130 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295105 p = 1 := by simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33235 p hg
    simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33237 (p : Pattern) (guard : d295047 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295042 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33228 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33238 (p : Pattern) (guard : d295048 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295047 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33237 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33239 (p : Pattern) (guard : d295049 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295048 p = 1 := by simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33238 p hg
    simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33240 (p : Pattern) (guard : d295050 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295049 p = 1 := by simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33239 p hg
    simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33241 (p : Pattern) (guard : d295051 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33232 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295050 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33240 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33242 (p : Pattern) (guard : d295052 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295051 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33241 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33243 (p : Pattern) (guard : d295053 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295052 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33242 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33244 (p : Pattern) (guard : d295067 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295053 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33243 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33245 (p : Pattern) (guard : d295131 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295130 p = 1 := by simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33236 p hg
    simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295067 p = 1 := by simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33244 p hg
    simpa only [d295131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33246 (p : Pattern) (guard : d295132 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295131 p = 1 := by simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33245 p hg
    simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33247 (p : Pattern) (guard : d295109 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33232 p hg
    simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33248 (p : Pattern) (guard : d295110 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295109 p = 1 := by simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33247 p hg
    simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33249 (p : Pattern) (guard : d295111 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295110 p = 1 := by simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33248 p hg
    simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295111, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
