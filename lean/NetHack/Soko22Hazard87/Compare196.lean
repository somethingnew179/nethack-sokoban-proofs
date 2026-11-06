import NetHack.Soko22Hazard87.Compare195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49000 (p : Pattern) (guard : d46882 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46881 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48999 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49001 (p : Pattern) (guard : d46883 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46880 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48998 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49002 (p : Pattern) (guard : d46884 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46881 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48999 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46883 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49001 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49003 (p : Pattern) (guard : d46885 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46882 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49000 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46884 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49002 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49004 (p : Pattern) (guard : d46886 p = 1) : d50577 p ≤ (1 : Int) + d371065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48967 p hg
    simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46885 p = 1 := by simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49003 p hg
    simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49005 (p : Pattern) (guard : d46887 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48966 p hg
    simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46886 p = 1 := by simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49004 p hg
    simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49006 (p : Pattern) (guard : d46888 p = 1) : d50553 p ≤ (1 : Int) + d371040 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48990 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48970 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49007 (p : Pattern) (guard : d46889 p = 1) : d50570 p ≤ (1 : Int) + d371058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49006 p hg
    simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48992 p hg
    simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49008 (p : Pattern) (guard : d46890 p = 1) : d50571 p ≤ (1 : Int) + d371059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46889 p = 1 := by simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49007 p hg
    simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48994 p hg
    simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49009 (p : Pattern) (guard : d46891 p = 1) : d50572 p ≤ (1 : Int) + d371060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48969 p hg
    simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46890 p = 1 := by simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49008 p hg
    simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49010 (p : Pattern) (guard : d46892 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46891 p = 1 := by simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49009 p hg
    simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48997 p hg
    simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49011 (p : Pattern) (guard : d46893 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46892 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49010 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49012 (p : Pattern) (guard : d46894 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46883 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49001 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46893 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49011 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49013 (p : Pattern) (guard : d46895 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46884 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49002 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46894 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49012 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49014 (p : Pattern) (guard : d46896 p = 1) : d50577 p ≤ (1 : Int) + d371065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48967 p hg
    simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46895 p = 1 := by simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49013 p hg
    simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49015 (p : Pattern) (guard : d46897 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48966 p hg
    simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46896 p = 1 := by simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49014 p hg
    simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49016 (p : Pattern) (guard : d46898 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46887 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49005 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46897 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49015 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49017 (p : Pattern) (guard : d0 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49018 (p : Pattern) (guard : d46899 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46897 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49015 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49019 (p : Pattern) (guard : d46900 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46898 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49016 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46899 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49018 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49020 (p : Pattern) (guard : d46901 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46900 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49019 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49021 (p : Pattern) (guard : d0 p = 1) : d50589 p ≤ (1 : Int) + d371077 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49022 (p : Pattern) (guard : d46902 p = 1) : d50590 p ≤ (1 : Int) + d371078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46901 p = 1 := by simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49020 p hg
    simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49021 p hg
    simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49023 (p : Pattern) (guard : d46903 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46902 p = 1 := by simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49022 p hg
    simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49024 (p : Pattern) (guard : d46904 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46899 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49018 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49025 (p : Pattern) (guard : d46905 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46904 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49024 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49026 (p : Pattern) (guard : d46906 p = 1) : d50590 p ≤ (1 : Int) + d371078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46905 p = 1 := by simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49025 p hg
    simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49021 p hg
    simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49027 (p : Pattern) (guard : d46907 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46906 p = 1 := by simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49026 p hg
    simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49028 (p : Pattern) (guard : d46908 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46903 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49023 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46907 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49027 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49029 (p : Pattern) (guard : d46909 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46908 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49028 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49030 (p : Pattern) (guard : d46910 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46909 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49029 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49031 (p : Pattern) (guard : d46911 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46910 p = 1 := by simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49030 p hg
    simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49032 (p : Pattern) (guard : d46912 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46907 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49027 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49033 (p : Pattern) (guard : d46913 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46912 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49032 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49034 (p : Pattern) (guard : d46914 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46913 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49033 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49035 (p : Pattern) (guard : d46915 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46914 p = 1 := by simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49034 p hg
    simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49036 (p : Pattern) (guard : d46916 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46911 p = 1 := by simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49031 p hg
    simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46915 p = 1 := by simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49035 p hg
    simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49037 (p : Pattern) (guard : d46917 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46916 p = 1 := by simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49036 p hg
    simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49038 (p : Pattern) (guard : d46918 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d46917 p = 1 := by simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49037 p hg
    simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49039 (p : Pattern) (guard : d46919 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46918 p = 1 := by simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49038 p hg
    simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49040 (p : Pattern) (guard : d46920 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46919 p = 1 := by simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49039 p hg
    simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49041 (p : Pattern) (guard : d46921 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46920 p = 1 := by simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49040 p hg
    simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49042 (p : Pattern) (guard : d46922 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46921 p = 1 := by simpa only [d46922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49041 p hg
    simpa only [d46922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49043 (p : Pattern) (guard : d46923 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 69 with
  | false =>
    have hg : d46922 p = 1 := by simpa only [d46923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49042 p hg
    simpa only [d46923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49044 (p : Pattern) (guard : d46924 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46910 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49030 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49045 (p : Pattern) (guard : d46925 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46914 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49034 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49046 (p : Pattern) (guard : d46926 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46924 p = 1 := by simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49044 p hg
    simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46925 p = 1 := by simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49045 p hg
    simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49047 (p : Pattern) (guard : d46927 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46926 p = 1 := by simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49046 p hg
    simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49048 (p : Pattern) (guard : d46928 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d46927 p = 1 := by simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49047 p hg
    simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49049 (p : Pattern) (guard : d46929 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46928 p = 1 := by simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49048 p hg
    simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49050 (p : Pattern) (guard : d46930 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46929 p = 1 := by simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49049 p hg
    simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49051 (p : Pattern) (guard : d46931 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d46920 p = 1 := by simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49040 p hg
    simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46930 p = 1 := by simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49050 p hg
    simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49052 (p : Pattern) (guard : d46932 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 70 with
  | false =>
    have hg : d46921 p = 1 := by simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49041 p hg
    simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46931 p = 1 := by simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49051 p hg
    simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49053 (p : Pattern) (guard : d46933 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 69 with
  | false =>
    have hg : d46932 p = 1 := by simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49052 p hg
    simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49054 (p : Pattern) (guard : d46934 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 51 with
  | false =>
    have hg : d46923 p = 1 := by simpa only [d46934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49043 p hg
    simpa only [d46934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46933 p = 1 := by simpa only [d46934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49053 p hg
    simpa only [d46934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49055 (p : Pattern) (guard : d46935 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46909 p = 1 := by simpa only [d46935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49029 p hg
    simpa only [d46935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49056 (p : Pattern) (guard : d46936 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46935 p = 1 := by simpa only [d46936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49055 p hg
    simpa only [d46936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49057 (p : Pattern) (guard : d46937 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46913 p = 1 := by simpa only [d46937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49033 p hg
    simpa only [d46937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49058 (p : Pattern) (guard : d46938 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46937 p = 1 := by simpa only [d46938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49057 p hg
    simpa only [d46938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49059 (p : Pattern) (guard : d46939 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46936 p = 1 := by simpa only [d46939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49056 p hg
    simpa only [d46939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46938 p = 1 := by simpa only [d46939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49058 p hg
    simpa only [d46939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49060 (p : Pattern) (guard : d46940 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46939 p = 1 := by simpa only [d46940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49059 p hg
    simpa only [d46940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49061 (p : Pattern) (guard : d46941 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d46940 p = 1 := by simpa only [d46941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49060 p hg
    simpa only [d46941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49062 (p : Pattern) (guard : d46942 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46941 p = 1 := by simpa only [d46942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49061 p hg
    simpa only [d46942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49063 (p : Pattern) (guard : d46943 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46908 p = 1 := by simpa only [d46943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49028 p hg
    simpa only [d46943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49064 (p : Pattern) (guard : d46944 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46943 p = 1 := by simpa only [d46944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49063 p hg
    simpa only [d46944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49065 (p : Pattern) (guard : d46945 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46944 p = 1 := by simpa only [d46945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49064 p hg
    simpa only [d46945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49066 (p : Pattern) (guard : d46946 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46912 p = 1 := by simpa only [d46946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49032 p hg
    simpa only [d46946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49067 (p : Pattern) (guard : d46947 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46946 p = 1 := by simpa only [d46947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49066 p hg
    simpa only [d46947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49068 (p : Pattern) (guard : d46948 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46947 p = 1 := by simpa only [d46948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49067 p hg
    simpa only [d46948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49069 (p : Pattern) (guard : d46949 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46945 p = 1 := by simpa only [d46949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49065 p hg
    simpa only [d46949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46948 p = 1 := by simpa only [d46949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49068 p hg
    simpa only [d46949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49070 (p : Pattern) (guard : d46950 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46949 p = 1 := by simpa only [d46950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49069 p hg
    simpa only [d46950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49071 (p : Pattern) (guard : d46951 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d46950 p = 1 := by simpa only [d46951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49070 p hg
    simpa only [d46951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49072 (p : Pattern) (guard : d46952 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46882 p = 1 := by simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49000 p hg
    simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49073 (p : Pattern) (guard : d46953 p = 1) : d50577 p ≤ (1 : Int) + d371065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46953, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48967 p hg
    simpa only [d46953, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46952 p = 1 := by simpa only [d46953, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49072 p hg
    simpa only [d46953, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49074 (p : Pattern) (guard : d46954 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46954, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48966 p hg
    simpa only [d46954, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46953 p = 1 := by simpa only [d46954, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49073 p hg
    simpa only [d46954, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49075 (p : Pattern) (guard : d46955 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46954 p = 1 := by simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49074 p hg
    simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46887 p = 1 := by simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49005 p hg
    simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49076 (p : Pattern) (guard : d46956 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46955 p = 1 := by simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49075 p hg
    simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46898 p = 1 := by simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49016 p hg
    simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49077 (p : Pattern) (guard : d46957 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46956 p = 1 := by simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49076 p hg
    simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49078 (p : Pattern) (guard : d46958 p = 1) : d50590 p ≤ (1 : Int) + d371078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46957 p = 1 := by simpa only [d46958, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49077 p hg
    simpa only [d46958, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46958, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49021 p hg
    simpa only [d46958, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49079 (p : Pattern) (guard : d46959 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46959, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d46959, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46958 p = 1 := by simpa only [d46959, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49078 p hg
    simpa only [d46959, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49080 (p : Pattern) (guard : d46960 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46959 p = 1 := by simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49079 p hg
    simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46903 p = 1 := by simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49023 p hg
    simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49081 (p : Pattern) (guard : d46961 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46960 p = 1 := by simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49080 p hg
    simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49082 (p : Pattern) (guard : d46962 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46961 p = 1 := by simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49081 p hg
    simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49083 (p : Pattern) (guard : d46963 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d46963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46962 p = 1 := by simpa only [d46963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49082 p hg
    simpa only [d46963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49084 (p : Pattern) (guard : d46964 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46963 p = 1 := by simpa only [d46964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49083 p hg
    simpa only [d46964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46911 p = 1 := by simpa only [d46964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49031 p hg
    simpa only [d46964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49085 (p : Pattern) (guard : d321682 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d46964 p = 1 := by simpa only [d321682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49084 p hg
    simpa only [d321682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d321682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49086 (p : Pattern) (guard : d47016 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46881 p = 1 := by simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48999 p hg
    simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49087 (p : Pattern) (guard : d47017 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47016 p = 1 := by simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49086 p hg
    simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49088 (p : Pattern) (guard : d47018 p = 1) : d50577 p ≤ (1 : Int) + d371065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47018, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48967 p hg
    simpa only [d47018, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47017 p = 1 := by simpa only [d47018, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49087 p hg
    simpa only [d47018, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49089 (p : Pattern) (guard : d47019 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47019, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48966 p hg
    simpa only [d47019, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47018 p = 1 := by simpa only [d47019, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49088 p hg
    simpa only [d47019, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49090 (p : Pattern) (guard : d47020 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47019 p = 1 := by simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49089 p hg
    simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49091 (p : Pattern) (guard : d47021 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46898 p = 1 := by simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49016 p hg
    simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47020 p = 1 := by simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49090 p hg
    simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49092 (p : Pattern) (guard : d47022 p = 1) : d50578 p ≤ (1 : Int) + d371066 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47021 p = 1 := by simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49091 p hg
    simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49017 p hg
    simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49093 (p : Pattern) (guard : d47023 p = 1) : d50590 p ≤ (1 : Int) + d371078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47022 p = 1 := by simpa only [d47023, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49092 p hg
    simpa only [d47023, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47023, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49021 p hg
    simpa only [d47023, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49094 (p : Pattern) (guard : d47024 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47024, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d47024, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47023 p = 1 := by simpa only [d47024, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49093 p hg
    simpa only [d47024, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49095 (p : Pattern) (guard : d47025 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 113 with
  | false =>
    have hg : d47024 p = 1 := by simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49094 p hg
    simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49096 (p : Pattern) (guard : d47026 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d47025 p = 1 := by simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49095 p hg
    simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49097 (p : Pattern) (guard : d47027 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d47026 p = 1 := by simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49096 p hg
    simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49098 (p : Pattern) (guard : d47028 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47027 p = 1 := by simpa only [d47028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49097 p hg
    simpa only [d47028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49099 (p : Pattern) (guard : d47029 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47028 p = 1 := by simpa only [d47029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49098 p hg
    simpa only [d47029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49100 (p : Pattern) (guard : d47030 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d47029 p = 1 := by simpa only [d47030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49099 p hg
    simpa only [d47030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49101 (p : Pattern) (guard : d321683 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d321682 p = 1 := by simpa only [d321683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49085 p hg
    simpa only [d321683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47030 p = 1 := by simpa only [d321683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49100 p hg
    simpa only [d321683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49102 (p : Pattern) (guard : d321684 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d46951 p = 1 := by simpa only [d321684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49071 p hg
    simpa only [d321684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321683 p = 1 := by simpa only [d321684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49101 p hg
    simpa only [d321684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49103 (p : Pattern) (guard : d321685 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d46942 p = 1 := by simpa only [d321685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49062 p hg
    simpa only [d321685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321684 p = 1 := by simpa only [d321685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49102 p hg
    simpa only [d321685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49104 (p : Pattern) (guard : d321686 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d321686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321685 p = 1 := by simpa only [d321686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49103 p hg
    simpa only [d321686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49105 (p : Pattern) (guard : d47035 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46935 p = 1 := by simpa only [d47035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49055 p hg
    simpa only [d47035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49106 (p : Pattern) (guard : d47036 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46937 p = 1 := by simpa only [d47036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49057 p hg
    simpa only [d47036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49107 (p : Pattern) (guard : d47037 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47035 p = 1 := by simpa only [d47037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49105 p hg
    simpa only [d47037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47036 p = 1 := by simpa only [d47037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49106 p hg
    simpa only [d47037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49108 (p : Pattern) (guard : d47038 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47037 p = 1 := by simpa only [d47038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49107 p hg
    simpa only [d47038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49109 (p : Pattern) (guard : d47039 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d47038 p = 1 := by simpa only [d47039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49108 p hg
    simpa only [d47039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49110 (p : Pattern) (guard : d47040 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47039 p = 1 := by simpa only [d47040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49109 p hg
    simpa only [d47040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49111 (p : Pattern) (guard : d47041 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46944 p = 1 := by simpa only [d47041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49064 p hg
    simpa only [d47041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49112 (p : Pattern) (guard : d47042 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46947 p = 1 := by simpa only [d47042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49067 p hg
    simpa only [d47042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49113 (p : Pattern) (guard : d47043 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47041 p = 1 := by simpa only [d47043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49111 p hg
    simpa only [d47043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47042 p = 1 := by simpa only [d47043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49112 p hg
    simpa only [d47043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49114 (p : Pattern) (guard : d47044 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47043 p = 1 := by simpa only [d47044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49113 p hg
    simpa only [d47044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49115 (p : Pattern) (guard : d47045 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d47044 p = 1 := by simpa only [d47045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49114 p hg
    simpa only [d47045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49116 (p : Pattern) (guard : d47046 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46962 p = 1 := by simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49082 p hg
    simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49117 (p : Pattern) (guard : d47047 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47046 p = 1 := by simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49116 p hg
    simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46924 p = 1 := by simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49044 p hg
    simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49118 (p : Pattern) (guard : d321687 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d47047 p = 1 := by simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49117 p hg
    simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49119 (p : Pattern) (guard : d47052 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d47027 p = 1 := by simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49097 p hg
    simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49120 (p : Pattern) (guard : d47053 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47052 p = 1 := by simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49119 p hg
    simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49121 (p : Pattern) (guard : d47054 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d47053 p = 1 := by simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49120 p hg
    simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49122 (p : Pattern) (guard : d321688 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d321687 p = 1 := by simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49118 p hg
    simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47054 p = 1 := by simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49121 p hg
    simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49123 (p : Pattern) (guard : d321689 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d47045 p = 1 := by simpa only [d321689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49115 p hg
    simpa only [d321689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321688 p = 1 := by simpa only [d321689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49122 p hg
    simpa only [d321689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49124 (p : Pattern) (guard : d321690 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d47040 p = 1 := by simpa only [d321690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49110 p hg
    simpa only [d321690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321689 p = 1 := by simpa only [d321690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49123 p hg
    simpa only [d321690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49125 (p : Pattern) (guard : d321691 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d321685 p = 1 := by simpa only [d321691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49103 p hg
    simpa only [d321691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321690 p = 1 := by simpa only [d321691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49124 p hg
    simpa only [d321691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49126 (p : Pattern) (guard : d321692 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 70 with
  | false =>
    have hg : d321686 p = 1 := by simpa only [d321692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49104 p hg
    simpa only [d321692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321691 p = 1 := by simpa only [d321692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49125 p hg
    simpa only [d321692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49127 (p : Pattern) (guard : d47060 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46915 p = 1 := by simpa only [d47060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49035 p hg
    simpa only [d47060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49128 (p : Pattern) (guard : d47061 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47060 p = 1 := by simpa only [d47061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49127 p hg
    simpa only [d47061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49129 (p : Pattern) (guard : d47062 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d47061 p = 1 := by simpa only [d47062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49128 p hg
    simpa only [d47062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49130 (p : Pattern) (guard : d47063 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47062 p = 1 := by simpa only [d47063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49129 p hg
    simpa only [d47063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49131 (p : Pattern) (guard : d47064 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47063 p = 1 := by simpa only [d47064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49130 p hg
    simpa only [d47064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49132 (p : Pattern) (guard : d47065 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d46920 p = 1 := by simpa only [d47065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49040 p hg
    simpa only [d47065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47064 p = 1 := by simpa only [d47065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49131 p hg
    simpa only [d47065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49133 (p : Pattern) (guard : d47066 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46925 p = 1 := by simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49045 p hg
    simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49134 (p : Pattern) (guard : d47067 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47066 p = 1 := by simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49133 p hg
    simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49135 (p : Pattern) (guard : d47068 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d47067 p = 1 := by simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49134 p hg
    simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49136 (p : Pattern) (guard : d47069 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47068 p = 1 := by simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49135 p hg
    simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49137 (p : Pattern) (guard : d47070 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47069 p = 1 := by simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49136 p hg
    simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49138 (p : Pattern) (guard : d47071 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d47064 p = 1 := by simpa only [d47071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49131 p hg
    simpa only [d47071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47070 p = 1 := by simpa only [d47071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49137 p hg
    simpa only [d47071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49139 (p : Pattern) (guard : d47072 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 70 with
  | false =>
    have hg : d47065 p = 1 := by simpa only [d47072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49132 p hg
    simpa only [d47072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47071 p = 1 := by simpa only [d47072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49138 p hg
    simpa only [d47072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49140 (p : Pattern) (guard : d321693 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 69 with
  | false =>
    have hg : d321692 p = 1 := by simpa only [d321693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49126 p hg
    simpa only [d321693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47072 p = 1 := by simpa only [d321693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49139 p hg
    simpa only [d321693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49141 (p : Pattern) (guard : d321694 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 51 with
  | false =>
    have hg : d321693 p = 1 := by simpa only [d321694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49140 p hg
    simpa only [d321694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d321694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49142 (p : Pattern) (guard : d321695 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  cases selected : p 50 with
  | false =>
    have hg : d46934 p = 1 := by simpa only [d321695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49054 p hg
    simpa only [d321695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321694 p = 1 := by simpa only [d321695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49141 p hg
    simpa only [d321695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49143 (p : Pattern) (guard : d0 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49144 (p : Pattern) (guard : d0 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49145 (p : Pattern) (guard : d0 p = 1) : d50671 p ≤ (1 : Int) + d371186 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49146 (p : Pattern) (guard : d0 p = 1) : d50631 p ≤ (1 : Int) + d371145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49147 (p : Pattern) (guard : d0 p = 1) : d50653 p ≤ (1 : Int) + d371168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49148 (p : Pattern) (guard : d0 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49149 (p : Pattern) (guard : d0 p = 1) : d50656 p ≤ (1 : Int) + d371171 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49150 (p : Pattern) (guard : d0 p = 1) : d50642 p ≤ (1 : Int) + d371157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49151 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (1 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49152 (p : Pattern) (guard : d0 p = 1) : d49565 p ≤ (1 : Int) + d371114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49153 (p : Pattern) (guard : d44880 p = 1) : d5 p ≤ (1 : Int) + d5 p := by
  omega
theorem compare49154 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (1 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49155 (p : Pattern) (guard : d46864 p = 1) : d47706 p ≤ (1 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49153 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49154 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49156 (p : Pattern) (guard : d46865 p = 1) : d47706 p ≤ (1 : Int) + d5 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49155 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49151 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49157 (p : Pattern) (guard : d0 p = 1) : d49560 p ≤ (1 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49158 (p : Pattern) (guard : d46866 p = 1) : d49561 p ≤ (1 : Int) + d371113 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49156 p hg
    simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49157 p hg
    simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49159 (p : Pattern) (guard : d0 p = 1) : d49564 p ≤ (1 : Int) + d370953 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49160 (p : Pattern) (guard : d46867 p = 1) : d49565 p ≤ (1 : Int) + d371114 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49158 p hg
    simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49159 p hg
    simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49161 (p : Pattern) (guard : d46868 p = 1) : d49565 p ≤ (1 : Int) + d371114 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49152 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49160 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49162 (p : Pattern) (guard : d46869 p = 1) : d50606 p ≤ (1 : Int) + d371115 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49151 p hg
    simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49161 p hg
    simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49163 (p : Pattern) (guard : d0 p = 1) : d50606 p ≤ (1 : Int) + d371115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49164 (p : Pattern) (guard : d46870 p = 1) : d50606 p ≤ (1 : Int) + d371115 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49162 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49163 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49165 (p : Pattern) (guard : d46871 p = 1) : d49565 p ≤ (1 : Int) + d371114 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49160 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49152 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49166 (p : Pattern) (guard : d46872 p = 1) : d50606 p ≤ (1 : Int) + d371115 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49151 p hg
    simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49165 p hg
    simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49167 (p : Pattern) (guard : d46873 p = 1) : d50606 p ≤ (1 : Int) + d371115 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49166 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49163 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49168 (p : Pattern) (guard : d46874 p = 1) : d50606 p ≤ (1 : Int) + d371115 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49164 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49167 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49169 (p : Pattern) (guard : d0 p = 1) : d49566 p ≤ (1 : Int) + d371156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49170 (p : Pattern) (guard : d46875 p = 1) : d50642 p ≤ (1 : Int) + d371157 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49168 p hg
    simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49169 p hg
    simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49171 (p : Pattern) (guard : d46876 p = 1) : d50642 p ≤ (1 : Int) + d371157 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49150 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49170 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49172 (p : Pattern) (guard : d0 p = 1) : d50530 p ≤ (1 : Int) + d371012 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49173 (p : Pattern) (guard : d46877 p = 1) : d50657 p ≤ (1 : Int) + d371172 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49171 p hg
    simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49172 p hg
    simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49174 (p : Pattern) (guard : d46878 p = 1) : d50658 p ≤ (1 : Int) + d371173 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46877 p = 1 := by simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49173 p hg
    simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49175 (p : Pattern) (guard : d46879 p = 1) : d50659 p ≤ (1 : Int) + d371174 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49149 p hg
    simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46878 p = 1 := by simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49174 p hg
    simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49176 (p : Pattern) (guard : d0 p = 1) : d50662 p ≤ (1 : Int) + d371177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49177 (p : Pattern) (guard : d46880 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46879 p = 1 := by simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49175 p hg
    simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49176 p hg
    simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49178 (p : Pattern) (guard : d46881 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46880 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49177 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49179 (p : Pattern) (guard : d46882 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46881 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49178 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49180 (p : Pattern) (guard : d46952 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46882 p = 1 := by simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49179 p hg
    simpa only [d46952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49181 (p : Pattern) (guard : d46953 p = 1) : d50664 p ≤ (1 : Int) + d371179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46953, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49147 p hg
    simpa only [d46953, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46952 p = 1 := by simpa only [d46953, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49180 p hg
    simpa only [d46953, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49182 (p : Pattern) (guard : d46954 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46954, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49146 p hg
    simpa only [d46954, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46953 p = 1 := by simpa only [d46954, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49181 p hg
    simpa only [d46954, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49183 (p : Pattern) (guard : d46883 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46880 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49177 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49184 (p : Pattern) (guard : d46884 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46881 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49178 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46883 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49183 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49185 (p : Pattern) (guard : d46885 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46882 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49179 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46884 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49184 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49186 (p : Pattern) (guard : d46886 p = 1) : d50664 p ≤ (1 : Int) + d371179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49147 p hg
    simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46885 p = 1 := by simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49185 p hg
    simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49187 (p : Pattern) (guard : d46887 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49146 p hg
    simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46886 p = 1 := by simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49186 p hg
    simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49188 (p : Pattern) (guard : d46955 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46954 p = 1 := by simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49182 p hg
    simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46887 p = 1 := by simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49187 p hg
    simpa only [d46955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49189 (p : Pattern) (guard : d46888 p = 1) : d50642 p ≤ (1 : Int) + d371157 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49170 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49150 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49190 (p : Pattern) (guard : d46889 p = 1) : d50657 p ≤ (1 : Int) + d371172 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49189 p hg
    simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49172 p hg
    simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49191 (p : Pattern) (guard : d46890 p = 1) : d50658 p ≤ (1 : Int) + d371173 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46889 p = 1 := by simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49190 p hg
    simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49192 (p : Pattern) (guard : d46891 p = 1) : d50659 p ≤ (1 : Int) + d371174 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49149 p hg
    simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46890 p = 1 := by simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49191 p hg
    simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49193 (p : Pattern) (guard : d46892 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46891 p = 1 := by simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49192 p hg
    simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49176 p hg
    simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49194 (p : Pattern) (guard : d46893 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46892 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49193 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49195 (p : Pattern) (guard : d46894 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46883 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49183 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46893 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49194 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49196 (p : Pattern) (guard : d46895 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46884 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49184 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46894 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49195 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49197 (p : Pattern) (guard : d46896 p = 1) : d50664 p ≤ (1 : Int) + d371179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49147 p hg
    simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46895 p = 1 := by simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49196 p hg
    simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49198 (p : Pattern) (guard : d46897 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49146 p hg
    simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46896 p = 1 := by simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49197 p hg
    simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49199 (p : Pattern) (guard : d46898 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46887 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49187 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46897 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49198 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49200 (p : Pattern) (guard : d46956 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46955 p = 1 := by simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49188 p hg
    simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46898 p = 1 := by simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49199 p hg
    simpa only [d46956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49201 (p : Pattern) (guard : d0 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49202 (p : Pattern) (guard : d46957 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46956 p = 1 := by simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49200 p hg
    simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d46957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49203 (p : Pattern) (guard : d0 p = 1) : d50672 p ≤ (1 : Int) + d371187 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49204 (p : Pattern) (guard : d46958 p = 1) : d50673 p ≤ (1 : Int) + d371188 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46957 p = 1 := by simpa only [d46958, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49202 p hg
    simpa only [d46958, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46958, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49203 p hg
    simpa only [d46958, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49205 (p : Pattern) (guard : d46959 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46959, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49145 p hg
    simpa only [d46959, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46958 p = 1 := by simpa only [d46959, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49204 p hg
    simpa only [d46959, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49206 (p : Pattern) (guard : d46899 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46897 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49198 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49207 (p : Pattern) (guard : d46900 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46898 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49199 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46899 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49206 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49208 (p : Pattern) (guard : d46901 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46900 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49207 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49209 (p : Pattern) (guard : d46902 p = 1) : d50673 p ≤ (1 : Int) + d371188 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46901 p = 1 := by simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49208 p hg
    simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49203 p hg
    simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49210 (p : Pattern) (guard : d46903 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49145 p hg
    simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46902 p = 1 := by simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49209 p hg
    simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49211 (p : Pattern) (guard : d46960 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46959 p = 1 := by simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49205 p hg
    simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46903 p = 1 := by simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49210 p hg
    simpa only [d46960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49212 (p : Pattern) (guard : d46961 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46960 p = 1 := by simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49211 p hg
    simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49213 (p : Pattern) (guard : d46962 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46961 p = 1 := by simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49212 p hg
    simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49214 (p : Pattern) (guard : d47046 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46962 p = 1 := by simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49213 p hg
    simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49215 (p : Pattern) (guard : d46904 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46899 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49206 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49216 (p : Pattern) (guard : d46905 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46904 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49215 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49217 (p : Pattern) (guard : d46906 p = 1) : d50673 p ≤ (1 : Int) + d371188 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46905 p = 1 := by simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49216 p hg
    simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49203 p hg
    simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49218 (p : Pattern) (guard : d46907 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49145 p hg
    simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46906 p = 1 := by simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49217 p hg
    simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49219 (p : Pattern) (guard : d46908 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46903 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49210 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46907 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49218 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49220 (p : Pattern) (guard : d46909 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46908 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49219 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49221 (p : Pattern) (guard : d46910 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46909 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49220 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49222 (p : Pattern) (guard : d46924 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46910 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49221 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49223 (p : Pattern) (guard : d47047 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47046 p = 1 := by simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49214 p hg
    simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46924 p = 1 := by simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49222 p hg
    simpa only [d47047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49224 (p : Pattern) (guard : d321687 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 90 with
  | false =>
    have hg : d47047 p = 1 := by simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49223 p hg
    simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d321687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49225 (p : Pattern) (guard : d47016 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46881 p = 1 := by simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49178 p hg
    simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d47016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49226 (p : Pattern) (guard : d47017 p = 1) : d50663 p ≤ (1 : Int) + d371178 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47016 p = 1 := by simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49225 p hg
    simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49148 p hg
    simpa only [d47017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49227 (p : Pattern) (guard : d47018 p = 1) : d50664 p ≤ (1 : Int) + d371179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47018, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49147 p hg
    simpa only [d47018, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47017 p = 1 := by simpa only [d47018, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49226 p hg
    simpa only [d47018, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49228 (p : Pattern) (guard : d47019 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47019, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49146 p hg
    simpa only [d47019, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47018 p = 1 := by simpa only [d47019, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49227 p hg
    simpa only [d47019, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49229 (p : Pattern) (guard : d47020 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47019 p = 1 := by simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49228 p hg
    simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d47020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49230 (p : Pattern) (guard : d47021 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46898 p = 1 := by simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49199 p hg
    simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47020 p = 1 := by simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49229 p hg
    simpa only [d47021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49231 (p : Pattern) (guard : d47022 p = 1) : d50665 p ≤ (1 : Int) + d371180 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47021 p = 1 := by simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49230 p hg
    simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49201 p hg
    simpa only [d47022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49232 (p : Pattern) (guard : d47023 p = 1) : d50673 p ≤ (1 : Int) + d371188 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47022 p = 1 := by simpa only [d47023, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49231 p hg
    simpa only [d47023, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47023, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49203 p hg
    simpa only [d47023, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49233 (p : Pattern) (guard : d47024 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47024, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49145 p hg
    simpa only [d47024, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47023 p = 1 := by simpa only [d47024, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49232 p hg
    simpa only [d47024, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49234 (p : Pattern) (guard : d47025 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 113 with
  | false =>
    have hg : d47024 p = 1 := by simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49233 p hg
    simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49235 (p : Pattern) (guard : d47026 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 96 with
  | false =>
    have hg : d47025 p = 1 := by simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49234 p hg
    simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49236 (p : Pattern) (guard : d47027 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 95 with
  | false =>
    have hg : d47026 p = 1 := by simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49235 p hg
    simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49237 (p : Pattern) (guard : d47052 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 93 with
  | false =>
    have hg : d47027 p = 1 := by simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49236 p hg
    simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49238 (p : Pattern) (guard : d47053 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47052 p = 1 := by simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49237 p hg
    simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49239 (p : Pattern) (guard : d47054 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 90 with
  | false =>
    have hg : d47053 p = 1 := by simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49238 p hg
    simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49240 (p : Pattern) (guard : d321688 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 89 with
  | false =>
    have hg : d321687 p = 1 := by simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49224 p hg
    simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47054 p = 1 := by simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49239 p hg
    simpa only [d321688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49241 (p : Pattern) (guard : d321696 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d321696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321688 p = 1 := by simpa only [d321696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49240 p hg
    simpa only [d321696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49242 (p : Pattern) (guard : d321697 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d321697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321696 p = 1 := by simpa only [d321697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49241 p hg
    simpa only [d321697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49243 (p : Pattern) (guard : d321698 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321698, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d321698, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321697 p = 1 := by simpa only [d321698, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49242 p hg
    simpa only [d321698, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49244 (p : Pattern) (guard : d321699 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49143 p hg
    simpa only [d321699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321698 p = 1 := by simpa only [d321699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49243 p hg
    simpa only [d321699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49245 (p : Pattern) (guard : d46912 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46907 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49218 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49246 (p : Pattern) (guard : d46913 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46912 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49245 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49247 (p : Pattern) (guard : d46914 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46913 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49246 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49248 (p : Pattern) (guard : d46925 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46914 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49247 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49249 (p : Pattern) (guard : d47066 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46925 p = 1 := by simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49248 p hg
    simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47066, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
