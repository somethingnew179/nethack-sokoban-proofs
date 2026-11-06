/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16940 (p : Pattern) (guard : d4967 p = 1) : d2003 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2003, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16939 p hg
    simpa only [d2003, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2003, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16894 p hg
    simpa only [d2003, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16941 (p : Pattern) (guard : d4967 p = 1) : d2004 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2004, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16936 p hg
    simpa only [d2004, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2004, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16940 p hg
    simpa only [d2004, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16942 (p : Pattern) (guard : d4967 p = 1) : d2005 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2005, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16941 p hg
    simpa only [d2005, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2005, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16926 p hg
    simpa only [d2005, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16943 (p : Pattern) (guard : d4967 p = 1) : d2006 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2006, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16926 p hg
    simpa only [d2006, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2006, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2006, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16944 (p : Pattern) (guard : d4967 p = 1) : d2007 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2007, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16942 p hg
    simpa only [d2007, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2007, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16943 p hg
    simpa only [d2007, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16945 (p : Pattern) (guard : d4967 p = 1) : d2008 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2008, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16933 p hg
    simpa only [d2008, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2008, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16944 p hg
    simpa only [d2008, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16946 (p : Pattern) (guard : d4967 p = 1) : d2009 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2009, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16843 p hg
    simpa only [d2009, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2009, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16945 p hg
    simpa only [d2009, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16947 (p : Pattern) (guard : d4967 p = 1) : d2010 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2010, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16863 p hg
    simpa only [d2010, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2010, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16946 p hg
    simpa only [d2010, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16948 (p : Pattern) (guard : d0 p = 1) : d2013 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16949 (p : Pattern) (guard : d4967 p = 1) : d2014 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2014, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4967, d2014, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2014, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16948 p hg
    simpa only [d4967, d2014, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16950 (p : Pattern) (guard : d4967 p = 1) : d2015 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2015, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16788 p hg
    simpa only [d2015, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2015, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16949 p hg
    simpa only [d2015, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16951 (p : Pattern) (guard : d4967 p = 1) : d2016 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2016, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16788 p hg
    simpa only [d2016, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2016, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16950 p hg
    simpa only [d2016, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16952 (p : Pattern) (guard : d4967 p = 1) : d2017 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2017, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16950 p hg
    simpa only [d2017, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2017, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16800 p hg
    simpa only [d2017, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16953 (p : Pattern) (guard : d4967 p = 1) : d2018 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2018, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16951 p hg
    simpa only [d2018, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2018, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16952 p hg
    simpa only [d2018, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16954 (p : Pattern) (guard : d4967 p = 1) : d2019 p ≤ (0 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2019, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2019, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2019, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16760 p hg
    simpa only [d4967, d2019, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16955 (p : Pattern) (guard : d4967 p = 1) : d2020 p ≤ (0 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2020, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16803 p hg
    simpa only [d2020, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2020, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16954 p hg
    simpa only [d2020, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16956 (p : Pattern) (guard : d4967 p = 1) : d2021 p ≤ (0 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2021, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2021, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2021, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16763 p hg
    simpa only [d4967, d2021, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16957 (p : Pattern) (guard : d4967 p = 1) : d2023 p ≤ (0 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2023, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16956 p hg
    simpa only [d2023, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2023, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15527 p hg
    simpa only [d2023, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16958 (p : Pattern) (guard : d4967 p = 1) : d2024 p ≤ (0 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2024, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16955 p hg
    simpa only [d2024, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2024, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16957 p hg
    simpa only [d2024, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16959 (p : Pattern) (guard : d4967 p = 1) : d2027 p ≤ (0 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2027, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16958 p hg
    simpa only [d2027, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2027, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15531 p hg
    simpa only [d2027, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16960 (p : Pattern) (guard : d4967 p = 1) : d2028 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2028, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16953 p hg
    simpa only [d2028, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2028, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16959 p hg
    simpa only [d2028, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16961 (p : Pattern) (guard : d0 p = 1) : d2031 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16962 (p : Pattern) (guard : d4967 p = 1) : d2032 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2032, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2032, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2032, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16961 p hg
    simpa only [d4967, d2032, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16963 (p : Pattern) (guard : d4967 p = 1) : d2033 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2033, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16788 p hg
    simpa only [d2033, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2033, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16962 p hg
    simpa only [d2033, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16964 (p : Pattern) (guard : d4967 p = 1) : d2034 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2034, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16949 p hg
    simpa only [d2034, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2034, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16799 p hg
    simpa only [d2034, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16965 (p : Pattern) (guard : d4967 p = 1) : d2035 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2035, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16963 p hg
    simpa only [d2035, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2035, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16964 p hg
    simpa only [d2035, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16966 (p : Pattern) (guard : d4967 p = 1) : d2036 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2036, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16949 p hg
    simpa only [d2036, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2036, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16776 p hg
    simpa only [d2036, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16967 (p : Pattern) (guard : d4967 p = 1) : d2037 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2037, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16966 p hg
    simpa only [d2037, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2037, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16779 p hg
    simpa only [d2037, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16968 (p : Pattern) (guard : d4967 p = 1) : d2038 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2038, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16965 p hg
    simpa only [d2038, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2038, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16967 p hg
    simpa only [d2038, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16969 (p : Pattern) (guard : d4967 p = 1) : d2039 p ≤ (0 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2039, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16954 p hg
    simpa only [d2039, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2039, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d2039, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16970 (p : Pattern) (guard : d4967 p = 1) : d2041 p ≤ (0 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2041, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16969 p hg
    simpa only [d2041, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2041, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15543 p hg
    simpa only [d2041, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16971 (p : Pattern) (guard : d4967 p = 1) : d2044 p ≤ (0 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2044, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16970 p hg
    simpa only [d2044, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2044, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15546 p hg
    simpa only [d2044, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16972 (p : Pattern) (guard : d4967 p = 1) : d2045 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2045, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16968 p hg
    simpa only [d2045, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2045, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16971 p hg
    simpa only [d2045, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16973 (p : Pattern) (guard : d4967 p = 1) : d2046 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2046, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16960 p hg
    simpa only [d2046, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2046, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16972 p hg
    simpa only [d2046, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16974 (p : Pattern) (guard : d0 p = 1) : d2049 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16975 (p : Pattern) (guard : d4967 p = 1) : d2050 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2050, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d2050, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2050, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16974 p hg
    simpa only [d4967, d2050, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16976 (p : Pattern) (guard : d0 p = 1) : d2055 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16977 (p : Pattern) (guard : d4967 p = 1) : d2056 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2056, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d2056, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2056, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16976 p hg
    simpa only [d4967, d2056, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16978 (p : Pattern) (guard : d4967 p = 1) : d2057 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16975 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16977 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16979 (p : Pattern) (guard : d4967 p = 1) : d2058 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2058, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16978 p hg
    simpa only [d2058, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2058, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16805 p hg
    simpa only [d2058, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16980 (p : Pattern) (guard : d4967 p = 1) : d2059 p ≤ (0 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2059, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16979 p hg
    simpa only [d2059, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2059, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16806 p hg
    simpa only [d2059, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16981 (p : Pattern) (guard : d0 p = 1) : d2062 p ≤ (0 : Int) + d192 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16982 (p : Pattern) (guard : d4967 p = 1) : d2063 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2063, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15558 p hg
    simpa only [d4967, d2063, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2063, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16981 p hg
    simpa only [d4967, d2063, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16983 (p : Pattern) (guard : d4967 p = 1) : d2064 p ≤ (0 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2064, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16795 p hg
    simpa only [d2064, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2064, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16982 p hg
    simpa only [d2064, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16984 (p : Pattern) (guard : d4967 p = 1) : d2065 p ≤ (0 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2065, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16983 p hg
    simpa only [d2065, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2065, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2065, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16985 (p : Pattern) (guard : d4967 p = 1) : d2066 p ≤ (0 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2066, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16984 p hg
    simpa only [d2066, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2066, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2066, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16986 (p : Pattern) (guard : d4967 p = 1) : d2067 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2067, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16980 p hg
    simpa only [d2067, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2067, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16985 p hg
    simpa only [d2067, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16987 (p : Pattern) (guard : d0 p = 1) : d2072 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16988 (p : Pattern) (guard : d4967 p = 1) : d2073 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2073, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2073, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2073, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16987 p hg
    simpa only [d4967, d2073, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16989 (p : Pattern) (guard : d4967 p = 1) : d2074 p ≤ (0 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16988 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16803 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16990 (p : Pattern) (guard : d4967 p = 1) : d2075 p ≤ (0 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2075, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16795 p hg
    simpa only [d2075, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2075, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d2075, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16991 (p : Pattern) (guard : d4967 p = 1) : d2076 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2076, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16989 p hg
    simpa only [d2076, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2076, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16990 p hg
    simpa only [d2076, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16992 (p : Pattern) (guard : d4967 p = 1) : d2077 p ≤ (0 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2077, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16991 p hg
    simpa only [d2077, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2077, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16816 p hg
    simpa only [d2077, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16993 (p : Pattern) (guard : d4967 p = 1) : d2078 p ≤ (0 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2078, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16982 p hg
    simpa only [d2078, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2078, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2078, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16994 (p : Pattern) (guard : d4967 p = 1) : d2079 p ≤ (0 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2079, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16993 p hg
    simpa only [d2079, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2079, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2079, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16995 (p : Pattern) (guard : d4967 p = 1) : d2080 p ≤ (0 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2080, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16994 p hg
    simpa only [d2080, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2080, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2080, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16996 (p : Pattern) (guard : d4967 p = 1) : d2081 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2081, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16992 p hg
    simpa only [d2081, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2081, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16995 p hg
    simpa only [d2081, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16997 (p : Pattern) (guard : d4967 p = 1) : d2082 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2082, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16986 p hg
    simpa only [d2082, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2082, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16996 p hg
    simpa only [d2082, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16998 (p : Pattern) (guard : d4967 p = 1) : d2083 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2083, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16973 p hg
    simpa only [d2083, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2083, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16997 p hg
    simpa only [d2083, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16999 (p : Pattern) (guard : d4967 p = 1) : d2084 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2084, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16997 p hg
    simpa only [d2084, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2084, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2084, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17000 (p : Pattern) (guard : d4967 p = 1) : d2085 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2085, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16998 p hg
    simpa only [d2085, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2085, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16999 p hg
    simpa only [d2085, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17001 (p : Pattern) (guard : d4967 p = 1) : d2086 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2086, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16855 p hg
    simpa only [d2086, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2086, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17000 p hg
    simpa only [d2086, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17002 (p : Pattern) (guard : d4967 p = 1) : d2087 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2087, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16843 p hg
    simpa only [d2087, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2087, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17001 p hg
    simpa only [d2087, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17003 (p : Pattern) (guard : d4967 p = 1) : d2088 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2088, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16869 p hg
    simpa only [d2088, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2088, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2088, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17004 (p : Pattern) (guard : d4967 p = 1) : d2089 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2089, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16886 p hg
    simpa only [d2089, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2089, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17003 p hg
    simpa only [d2089, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17005 (p : Pattern) (guard : d4967 p = 1) : d2090 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2090, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17003 p hg
    simpa only [d2090, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2090, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2090, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17006 (p : Pattern) (guard : d4967 p = 1) : d2091 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2091, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17004 p hg
    simpa only [d2091, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2091, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17005 p hg
    simpa only [d2091, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17007 (p : Pattern) (guard : d4967 p = 1) : d2093 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2093, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16892 p hg
    simpa only [d2093, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2093, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15585 p hg
    simpa only [d2093, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17008 (p : Pattern) (guard : d4967 p = 1) : d2095 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2095, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17007 p hg
    simpa only [d2095, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2095, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15587 p hg
    simpa only [d2095, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17009 (p : Pattern) (guard : d4967 p = 1) : d2096 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2096, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17006 p hg
    simpa only [d2096, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2096, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17008 p hg
    simpa only [d2096, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17010 (p : Pattern) (guard : d4967 p = 1) : d2097 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2097, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16882 p hg
    simpa only [d2097, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2097, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17009 p hg
    simpa only [d2097, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17011 (p : Pattern) (guard : d4967 p = 1) : d2098 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2098, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d2098, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2098, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2098, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17012 (p : Pattern) (guard : d4967 p = 1) : d2099 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2099, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16916 p hg
    simpa only [d2099, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2099, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17011 p hg
    simpa only [d2099, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17013 (p : Pattern) (guard : d4967 p = 1) : d2100 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2100, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17011 p hg
    simpa only [d2100, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2100, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2100, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17014 (p : Pattern) (guard : d4967 p = 1) : d2101 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2101, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17012 p hg
    simpa only [d2101, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2101, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17013 p hg
    simpa only [d2101, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17015 (p : Pattern) (guard : d4967 p = 1) : d2102 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2102, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17014 p hg
    simpa only [d2102, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2102, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16924 p hg
    simpa only [d2102, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17016 (p : Pattern) (guard : d4967 p = 1) : d2103 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2103, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16915 p hg
    simpa only [d2103, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2103, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17015 p hg
    simpa only [d2103, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17017 (p : Pattern) (guard : d4967 p = 1) : d2104 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2104, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17010 p hg
    simpa only [d2104, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2104, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17016 p hg
    simpa only [d2104, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17018 (p : Pattern) (guard : d4967 p = 1) : d2105 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2105, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17016 p hg
    simpa only [d2105, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2105, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16931 p hg
    simpa only [d2105, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17019 (p : Pattern) (guard : d4967 p = 1) : d2106 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2106, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17017 p hg
    simpa only [d2106, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2106, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17018 p hg
    simpa only [d2106, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17020 (p : Pattern) (guard : d0 p = 1) : d2109 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17021 (p : Pattern) (guard : d4967 p = 1) : d2110 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2110, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d2110, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2110, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17020 p hg
    simpa only [d4967, d2110, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17022 (p : Pattern) (guard : d4967 p = 1) : d2111 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2111, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17021 p hg
    simpa only [d2111, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2111, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d2111, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17023 (p : Pattern) (guard : d4967 p = 1) : d2112 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2112, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16898 p hg
    simpa only [d2112, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2112, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17022 p hg
    simpa only [d2112, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17024 (p : Pattern) (guard : d4967 p = 1) : d2113 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2113, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16900 p hg
    simpa only [d2113, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2113, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d2113, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17025 (p : Pattern) (guard : d4967 p = 1) : d2114 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2114, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17024 p hg
    simpa only [d2114, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2114, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16872 p hg
    simpa only [d2114, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17026 (p : Pattern) (guard : d4967 p = 1) : d2115 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2115, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17023 p hg
    simpa only [d2115, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2115, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17025 p hg
    simpa only [d2115, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17027 (p : Pattern) (guard : d4967 p = 1) : d2116 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2116, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d2116, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2116, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16877 p hg
    simpa only [d4967, d2116, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17028 (p : Pattern) (guard : d4967 p = 1) : d2117 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2117, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d2117, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2117, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17027 p hg
    simpa only [d2117, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17029 (p : Pattern) (guard : d4967 p = 1) : d2118 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2118, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17028 p hg
    simpa only [d2118, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2118, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15585 p hg
    simpa only [d2118, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17030 (p : Pattern) (guard : d4967 p = 1) : d2122 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2122, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17029 p hg
    simpa only [d2122, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2122, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15615 p hg
    simpa only [d2122, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17031 (p : Pattern) (guard : d4967 p = 1) : d2123 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2123, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17026 p hg
    simpa only [d2123, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2123, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17030 p hg
    simpa only [d2123, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17032 (p : Pattern) (guard : d0 p = 1) : d2126 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17033 (p : Pattern) (guard : d4967 p = 1) : d2127 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2127, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d2127, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2127, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17032 p hg
    simpa only [d4967, d2127, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17034 (p : Pattern) (guard : d4967 p = 1) : d2128 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2128, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17021 p hg
    simpa only [d2128, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2128, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17033 p hg
    simpa only [d2128, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17035 (p : Pattern) (guard : d0 p = 1) : d2131 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17036 (p : Pattern) (guard : d4967 p = 1) : d2132 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2132, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d2132, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2132, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17035 p hg
    simpa only [d4967, d2132, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17037 (p : Pattern) (guard : d4967 p = 1) : d2133 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2133, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17036 p hg
    simpa only [d2133, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2133, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2133, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17038 (p : Pattern) (guard : d4967 p = 1) : d2134 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2134, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17034 p hg
    simpa only [d2134, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2134, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17037 p hg
    simpa only [d2134, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17039 (p : Pattern) (guard : d0 p = 1) : d2137 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17040 (p : Pattern) (guard : d4967 p = 1) : d2138 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2138, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d2138, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2138, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17039 p hg
    simpa only [d4967, d2138, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17041 (p : Pattern) (guard : d4967 p = 1) : d2139 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2139, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17040 p hg
    simpa only [d2139, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2139, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2139, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17042 (p : Pattern) (guard : d4967 p = 1) : d2140 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2140, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17041 p hg
    simpa only [d2140, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2140, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2140, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17043 (p : Pattern) (guard : d4967 p = 1) : d2141 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2141, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17038 p hg
    simpa only [d2141, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2141, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17042 p hg
    simpa only [d2141, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17044 (p : Pattern) (guard : d4967 p = 1) : d2142 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2142, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d2142, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2142, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16877 p hg
    simpa only [d4967, d2142, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17045 (p : Pattern) (guard : d4967 p = 1) : d2143 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2143, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17044 p hg
    simpa only [d2143, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2143, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15437 p hg
    simpa only [d2143, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17046 (p : Pattern) (guard : d4967 p = 1) : d2144 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2144, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17045 p hg
    simpa only [d2144, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2144, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15614 p hg
    simpa only [d2144, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17047 (p : Pattern) (guard : d4967 p = 1) : d2146 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2146, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17046 p hg
    simpa only [d2146, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2146, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15633 p hg
    simpa only [d2146, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17048 (p : Pattern) (guard : d4967 p = 1) : d2147 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2147, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17043 p hg
    simpa only [d2147, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2147, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17047 p hg
    simpa only [d2147, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17049 (p : Pattern) (guard : d4967 p = 1) : d2148 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2148, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17031 p hg
    simpa only [d2148, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2148, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17048 p hg
    simpa only [d2148, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17050 (p : Pattern) (guard : d4967 p = 1) : d2149 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16900 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16903 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17051 (p : Pattern) (guard : d4967 p = 1) : d2150 p ≤ (0 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2150, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d2150, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2150, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d2150, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17052 (p : Pattern) (guard : d4967 p = 1) : d2151 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2151, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17050 p hg
    simpa only [d2151, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2151, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17051 p hg
    simpa only [d2151, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17053 (p : Pattern) (guard : d4967 p = 1) : d2152 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2152, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17052 p hg
    simpa only [d2152, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2152, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16920 p hg
    simpa only [d2152, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17054 (p : Pattern) (guard : d4967 p = 1) : d2153 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2153, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17053 p hg
    simpa only [d2153, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2153, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16924 p hg
    simpa only [d2153, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17055 (p : Pattern) (guard : d0 p = 1) : d2158 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17056 (p : Pattern) (guard : d4967 p = 1) : d2159 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2159, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d2159, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2159, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17055 p hg
    simpa only [d4967, d2159, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17057 (p : Pattern) (guard : d4967 p = 1) : d2160 p ≤ (0 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17056 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17058 (p : Pattern) (guard : d4967 p = 1) : d2161 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2161, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17057 p hg
    simpa only [d2161, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2161, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17011 p hg
    simpa only [d2161, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17059 (p : Pattern) (guard : d4967 p = 1) : d2162 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2162, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17058 p hg
    simpa only [d2162, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2162, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16923 p hg
    simpa only [d2162, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17060 (p : Pattern) (guard : d4967 p = 1) : d2163 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2163, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16800 p hg
    simpa only [d2163, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2163, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2163, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17061 (p : Pattern) (guard : d4967 p = 1) : d2164 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2164, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17060 p hg
    simpa only [d2164, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2164, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2164, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17062 (p : Pattern) (guard : d4967 p = 1) : d2165 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2165, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17059 p hg
    simpa only [d2165, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2165, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17061 p hg
    simpa only [d2165, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17063 (p : Pattern) (guard : d4967 p = 1) : d2166 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2166, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17054 p hg
    simpa only [d2166, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2166, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17062 p hg
    simpa only [d2166, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17064 (p : Pattern) (guard : d4967 p = 1) : d2167 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2167, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17049 p hg
    simpa only [d2167, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2167, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17063 p hg
    simpa only [d2167, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17065 (p : Pattern) (guard : d4967 p = 1) : d2168 p ≤ (0 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2168, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d2168, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2168, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16799 p hg
    simpa only [d2168, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17066 (p : Pattern) (guard : d4967 p = 1) : d2169 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2169, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17050 p hg
    simpa only [d2169, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2169, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17065 p hg
    simpa only [d2169, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17067 (p : Pattern) (guard : d4967 p = 1) : d2170 p ≤ (0 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2170, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d2170, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2170, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16799 p hg
    simpa only [d2170, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17068 (p : Pattern) (guard : d4967 p = 1) : d2171 p ≤ (0 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2171, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17067 p hg
    simpa only [d2171, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2171, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2171, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17069 (p : Pattern) (guard : d4967 p = 1) : d2172 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2172, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17066 p hg
    simpa only [d2172, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2172, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17068 p hg
    simpa only [d2172, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17070 (p : Pattern) (guard : d4967 p = 1) : d2173 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2173, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16911 p hg
    simpa only [d2173, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2173, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d2173, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17071 (p : Pattern) (guard : d4967 p = 1) : d2174 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2174, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17070 p hg
    simpa only [d2174, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2174, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2174, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17072 (p : Pattern) (guard : d4967 p = 1) : d2175 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2175, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17071 p hg
    simpa only [d2175, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2175, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2175, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17073 (p : Pattern) (guard : d4967 p = 1) : d2176 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2176, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17069 p hg
    simpa only [d2176, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2176, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17072 p hg
    simpa only [d2176, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17074 (p : Pattern) (guard : d4967 p = 1) : d2177 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2177, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17073 p hg
    simpa only [d2177, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2177, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17062 p hg
    simpa only [d2177, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17075 (p : Pattern) (guard : d4967 p = 1) : d2178 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2178, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17074 p hg
    simpa only [d2178, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2178, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2178, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17076 (p : Pattern) (guard : d4967 p = 1) : d2179 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2179, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17064 p hg
    simpa only [d2179, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2179, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17075 p hg
    simpa only [d2179, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17077 (p : Pattern) (guard : d4967 p = 1) : d2180 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2180, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17019 p hg
    simpa only [d2180, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2180, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17076 p hg
    simpa only [d2180, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17078 (p : Pattern) (guard : d4967 p = 1) : d2181 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2181, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16843 p hg
    simpa only [d2181, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2181, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17077 p hg
    simpa only [d2181, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17079 (p : Pattern) (guard : d4967 p = 1) : d2182 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2182, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17002 p hg
    simpa only [d2182, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2182, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17078 p hg
    simpa only [d2182, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
