import NetHack.Soko22Hazard87.Compare007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2000 (p : Pattern) (guard : d61211 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 260 with
  | false =>
    have hg : d61210 p = 1 := by simpa only [d61211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1999 p hg
    simpa only [d61211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2001 (p : Pattern) (guard : d61212 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 259 with
  | false =>
    have hg : d61211 p = 1 := by simpa only [d61212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2000 p hg
    simpa only [d61212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2002 (p : Pattern) (guard : d61213 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 258 with
  | false =>
    have hg : d61212 p = 1 := by simpa only [d61213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2001 p hg
    simpa only [d61213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2003 (p : Pattern) (guard : d61214 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 257 with
  | false =>
    have hg : d61213 p = 1 := by simpa only [d61214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2002 p hg
    simpa only [d61214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2004 (p : Pattern) (guard : d61215 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 256 with
  | false =>
    have hg : d61214 p = 1 := by simpa only [d61215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d61215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2005 (p : Pattern) (guard : d61216 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 255 with
  | false =>
    have hg : d61215 p = 1 := by simpa only [d61216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d61216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2006 (p : Pattern) (guard : d61217 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 254 with
  | false =>
    have hg : d61216 p = 1 := by simpa only [d61217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2005 p hg
    simpa only [d61217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2007 (p : Pattern) (guard : d61218 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 253 with
  | false =>
    have hg : d61217 p = 1 := by simpa only [d61218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2006 p hg
    simpa only [d61218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2008 (p : Pattern) (guard : d61219 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 252 with
  | false =>
    have hg : d61218 p = 1 := by simpa only [d61219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2007 p hg
    simpa only [d61219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2009 (p : Pattern) (guard : d61220 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 251 with
  | false =>
    have hg : d61219 p = 1 := by simpa only [d61220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2008 p hg
    simpa only [d61220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2010 (p : Pattern) (guard : d61221 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 250 with
  | false =>
    have hg : d61220 p = 1 := by simpa only [d61221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2009 p hg
    simpa only [d61221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2011 (p : Pattern) (guard : d61222 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 249 with
  | false =>
    have hg : d61221 p = 1 := by simpa only [d61222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d61222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2012 (p : Pattern) (guard : d61223 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 245 with
  | false =>
    have hg : d61222 p = 1 := by simpa only [d61223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2011 p hg
    simpa only [d61223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2013 (p : Pattern) (guard : d61224 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 200 with
  | false =>
    have hg : d61223 p = 1 := by simpa only [d61224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2012 p hg
    simpa only [d61224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2014 (p : Pattern) (guard : d61225 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 199 with
  | false =>
    have hg : d61224 p = 1 := by simpa only [d61225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2013 p hg
    simpa only [d61225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2015 (p : Pattern) (guard : d61226 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 186 with
  | false =>
    have hg : d61225 p = 1 := by simpa only [d61226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2014 p hg
    simpa only [d61226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2016 (p : Pattern) (guard : d61227 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 185 with
  | false =>
    have hg : d61226 p = 1 := by simpa only [d61227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2015 p hg
    simpa only [d61227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2017 (p : Pattern) (guard : d61228 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 184 with
  | false =>
    have hg : d61227 p = 1 := by simpa only [d61228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2016 p hg
    simpa only [d61228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2018 (p : Pattern) (guard : d61229 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 181 with
  | false =>
    have hg : d61228 p = 1 := by simpa only [d61229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d61229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2019 (p : Pattern) (guard : d61230 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 177 with
  | false =>
    have hg : d61229 p = 1 := by simpa only [d61230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2018 p hg
    simpa only [d61230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2020 (p : Pattern) (guard : d61231 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 164 with
  | false =>
    have hg : d61230 p = 1 := by simpa only [d61231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2019 p hg
    simpa only [d61231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2021 (p : Pattern) (guard : d61232 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 156 with
  | false =>
    have hg : d61231 p = 1 := by simpa only [d61232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2020 p hg
    simpa only [d61232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2022 (p : Pattern) (guard : d61233 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 155 with
  | false =>
    have hg : d61232 p = 1 := by simpa only [d61233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2021 p hg
    simpa only [d61233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2023 (p : Pattern) (guard : d61234 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 134 with
  | false =>
    have hg : d61233 p = 1 := by simpa only [d61234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d61234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2024 (p : Pattern) (guard : d61235 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 133 with
  | false =>
    have hg : d61234 p = 1 := by simpa only [d61235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2023 p hg
    simpa only [d61235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2025 (p : Pattern) (guard : d61236 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 120 with
  | false =>
    have hg : d61235 p = 1 := by simpa only [d61236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2024 p hg
    simpa only [d61236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2026 (p : Pattern) (guard : d61237 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 118 with
  | false =>
    have hg : d61236 p = 1 := by simpa only [d61237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d61237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2027 (p : Pattern) (guard : d61238 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 114 with
  | false =>
    have hg : d61237 p = 1 := by simpa only [d61238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2026 p hg
    simpa only [d61238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2028 (p : Pattern) (guard : d61239 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 111 with
  | false =>
    have hg : d61238 p = 1 := by simpa only [d61239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2027 p hg
    simpa only [d61239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2029 (p : Pattern) (guard : d61240 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 98 with
  | false =>
    have hg : d61239 p = 1 := by simpa only [d61240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2028 p hg
    simpa only [d61240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2030 (p : Pattern) (guard : d61241 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 97 with
  | false =>
    have hg : d61240 p = 1 := by simpa only [d61241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2029 p hg
    simpa only [d61241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2031 (p : Pattern) (guard : d61242 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 94 with
  | false =>
    have hg : d61241 p = 1 := by simpa only [d61242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2030 p hg
    simpa only [d61242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2032 (p : Pattern) (guard : d61243 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 76 with
  | false =>
    have hg : d61242 p = 1 := by simpa only [d61243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d61243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2033 (p : Pattern) (guard : d61244 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 67 with
  | false =>
    have hg : d61243 p = 1 := by simpa only [d61244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2032 p hg
    simpa only [d61244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2034 (p : Pattern) (guard : d61245 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 52 with
  | false =>
    have hg : d61244 p = 1 := by simpa only [d61245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d61245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2035 (p : Pattern) (guard : d61246 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 47 with
  | false =>
    have hg : d61245 p = 1 := by simpa only [d61246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2034 p hg
    simpa only [d61246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2036 (p : Pattern) (guard : d61247 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 46 with
  | false =>
    have hg : d61246 p = 1 := by simpa only [d61247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2035 p hg
    simpa only [d61247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2037 (p : Pattern) (guard : d61248 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 45 with
  | false =>
    have hg : d61247 p = 1 := by simpa only [d61248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2036 p hg
    simpa only [d61248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2038 (p : Pattern) (guard : d61249 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 30 with
  | false =>
    have hg : d61248 p = 1 := by simpa only [d61249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2037 p hg
    simpa only [d61249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2039 (p : Pattern) (guard : d61250 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 29 with
  | false =>
    have hg : d61249 p = 1 := by simpa only [d61250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d61250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2040 (p : Pattern) (guard : d61251 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 28 with
  | false =>
    have hg : d61250 p = 1 := by simpa only [d61251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2039 p hg
    simpa only [d61251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2041 (p : Pattern) (guard : d61252 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 27 with
  | false =>
    have hg : d61251 p = 1 := by simpa only [d61252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2040 p hg
    simpa only [d61252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2042 (p : Pattern) (guard : d61253 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 25 with
  | false =>
    have hg : d61252 p = 1 := by simpa only [d61253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2041 p hg
    simpa only [d61253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2043 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2044 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2045 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-1 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2046 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-2 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2047 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2048 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2049 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2050 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2051 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2052 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-1 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2053 (p : Pattern) (guard : d0 p = 1) : d48080 p ≤ (-2 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2054 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2055 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2056 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-1 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2057 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-2 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2058 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2059 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-2 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2060 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2061 (p : Pattern) (guard : d59 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2062 (p : Pattern) (guard : d0 p = 1) : d48046 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2063 (p : Pattern) (guard : d2519 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d59 p = 1 := by simpa only [d2519, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2061 p hg
    simpa only [d2519, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2519, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d2519, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2064 (p : Pattern) (guard : d0 p = 1) : d48082 p ≤ (0 : Int) + d47910 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2065 (p : Pattern) (guard : d2520 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d2519 p = 1 := by simpa only [d2520, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2063 p hg
    simpa only [d2520, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2520, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d2520, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2066 (p : Pattern) (guard : d2521 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2520 p = 1 := by simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2065 p hg
    simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2067 (p : Pattern) (guard : d2522 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2521 p = 1 := by simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2066 p hg
    simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2068 (p : Pattern) (guard : d2523 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2522 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2067 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2069 (p : Pattern) (guard : d2524 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2523 p = 1 := by simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2068 p hg
    simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2070 (p : Pattern) (guard : d64416 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2071 (p : Pattern) (guard : d64417 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64416 p = 1 := by simpa only [d64417, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2070 p hg
    simpa only [d64417, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64417, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d64417, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2072 (p : Pattern) (guard : d64418 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64417 p = 1 := by simpa only [d64418, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2071 p hg
    simpa only [d64418, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64418, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d64418, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2073 (p : Pattern) (guard : d64419 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64418 p = 1 := by simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2072 p hg
    simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2074 (p : Pattern) (guard : d64420 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64419 p = 1 := by simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2073 p hg
    simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2075 (p : Pattern) (guard : d64421 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64420 p = 1 := by simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2074 p hg
    simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2076 (p : Pattern) (guard : d64422 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64421 p = 1 := by simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2075 p hg
    simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2077 (p : Pattern) (guard : d64423 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d2524 p = 1 := by simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2069 p hg
    simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64422 p = 1 := by simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2076 p hg
    simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2078 (p : Pattern) (guard : d64424 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2079 (p : Pattern) (guard : d64425 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64424 p = 1 := by simpa only [d64425, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2078 p hg
    simpa only [d64425, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64425, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d64425, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2080 (p : Pattern) (guard : d64426 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64425 p = 1 := by simpa only [d64426, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2079 p hg
    simpa only [d64426, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64426, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d64426, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2081 (p : Pattern) (guard : d64427 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64426 p = 1 := by simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2082 (p : Pattern) (guard : d64428 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64427 p = 1 := by simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2081 p hg
    simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2083 (p : Pattern) (guard : d64429 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64428 p = 1 := by simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2082 p hg
    simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2084 (p : Pattern) (guard : d64430 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64429 p = 1 := by simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2083 p hg
    simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2085 (p : Pattern) (guard : d64431 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64430 p = 1 := by simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2084 p hg
    simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2086 (p : Pattern) (guard : d64432 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d64423 p = 1 := by simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2077 p hg
    simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64431 p = 1 := by simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2085 p hg
    simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2087 (p : Pattern) (guard : d64433 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2088 (p : Pattern) (guard : d64434 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64433 p = 1 := by simpa only [d64434, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2087 p hg
    simpa only [d64434, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64434, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d64434, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2089 (p : Pattern) (guard : d64435 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64434 p = 1 := by simpa only [d64435, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2088 p hg
    simpa only [d64435, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64435, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d64435, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2090 (p : Pattern) (guard : d64436 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64435 p = 1 := by simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2089 p hg
    simpa only [d64436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2091 (p : Pattern) (guard : d64437 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64436 p = 1 := by simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2090 p hg
    simpa only [d64437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2092 (p : Pattern) (guard : d64438 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64437 p = 1 := by simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2091 p hg
    simpa only [d64438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2093 (p : Pattern) (guard : d64439 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64438 p = 1 := by simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2092 p hg
    simpa only [d64439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2094 (p : Pattern) (guard : d64440 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64439 p = 1 := by simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2093 p hg
    simpa only [d64440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2095 (p : Pattern) (guard : d64441 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64440 p = 1 := by simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2094 p hg
    simpa only [d64441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2096 (p : Pattern) (guard : d64442 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d64432 p = 1 := by simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2086 p hg
    simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64441 p = 1 := by simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2095 p hg
    simpa only [d64442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2097 (p : Pattern) (guard : d64443 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2098 (p : Pattern) (guard : d64444 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64443 p = 1 := by simpa only [d64444, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2097 p hg
    simpa only [d64444, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64444, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d64444, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2099 (p : Pattern) (guard : d64445 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64444 p = 1 := by simpa only [d64445, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2098 p hg
    simpa only [d64445, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64445, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d64445, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2100 (p : Pattern) (guard : d64446 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64445 p = 1 := by simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d64446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2101 (p : Pattern) (guard : d64447 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64446 p = 1 := by simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2100 p hg
    simpa only [d64447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2102 (p : Pattern) (guard : d64448 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64447 p = 1 := by simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2101 p hg
    simpa only [d64448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2103 (p : Pattern) (guard : d64449 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64448 p = 1 := by simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2102 p hg
    simpa only [d64449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2104 (p : Pattern) (guard : d64450 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64449 p = 1 := by simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2103 p hg
    simpa only [d64450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2105 (p : Pattern) (guard : d64451 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64450 p = 1 := by simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2104 p hg
    simpa only [d64451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2106 (p : Pattern) (guard : d64452 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64451 p = 1 := by simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d64452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2107 (p : Pattern) (guard : d64453 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d64442 p = 1 := by simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2096 p hg
    simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64452 p = 1 := by simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2106 p hg
    simpa only [d64453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2108 (p : Pattern) (guard : d64454 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2109 (p : Pattern) (guard : d64455 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64454 p = 1 := by simpa only [d64455, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2108 p hg
    simpa only [d64455, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64455, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d64455, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2110 (p : Pattern) (guard : d64456 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64455 p = 1 := by simpa only [d64456, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d64456, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64456, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d64456, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2111 (p : Pattern) (guard : d64457 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64456 p = 1 := by simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2110 p hg
    simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2112 (p : Pattern) (guard : d64458 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64457 p = 1 := by simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2113 (p : Pattern) (guard : d64459 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64458 p = 1 := by simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2112 p hg
    simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2114 (p : Pattern) (guard : d64460 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64459 p = 1 := by simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2113 p hg
    simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2115 (p : Pattern) (guard : d64461 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64460 p = 1 := by simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2114 p hg
    simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2116 (p : Pattern) (guard : d64462 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64461 p = 1 := by simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2117 (p : Pattern) (guard : d64463 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64462 p = 1 := by simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2116 p hg
    simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2118 (p : Pattern) (guard : d64464 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64463 p = 1 := by simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2119 (p : Pattern) (guard : d64465 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d64453 p = 1 := by simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2107 p hg
    simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64464 p = 1 := by simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2118 p hg
    simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2120 (p : Pattern) (guard : d64466 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2121 (p : Pattern) (guard : d64467 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64466 p = 1 := by simpa only [d64467, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d64467, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64467, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d64467, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2122 (p : Pattern) (guard : d64468 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64467 p = 1 := by simpa only [d64468, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2121 p hg
    simpa only [d64468, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64468, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d64468, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2123 (p : Pattern) (guard : d64469 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64468 p = 1 := by simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2122 p hg
    simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2124 (p : Pattern) (guard : d64470 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64469 p = 1 := by simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2123 p hg
    simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2125 (p : Pattern) (guard : d64471 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64470 p = 1 := by simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2126 (p : Pattern) (guard : d64472 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64471 p = 1 := by simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2125 p hg
    simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2127 (p : Pattern) (guard : d64473 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64472 p = 1 := by simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2126 p hg
    simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2128 (p : Pattern) (guard : d64474 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64473 p = 1 := by simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2127 p hg
    simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2129 (p : Pattern) (guard : d64475 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64474 p = 1 := by simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2128 p hg
    simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2130 (p : Pattern) (guard : d64476 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64475 p = 1 := by simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2129 p hg
    simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2131 (p : Pattern) (guard : d64477 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64476 p = 1 := by simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2132 (p : Pattern) (guard : d64478 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d64465 p = 1 := by simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2119 p hg
    simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64477 p = 1 := by simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2131 p hg
    simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2133 (p : Pattern) (guard : d64479 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2134 (p : Pattern) (guard : d64480 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64479 p = 1 := by simpa only [d64480, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2133 p hg
    simpa only [d64480, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64480, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d64480, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2135 (p : Pattern) (guard : d64481 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64480 p = 1 := by simpa only [d64481, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2134 p hg
    simpa only [d64481, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64481, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d64481, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2136 (p : Pattern) (guard : d64482 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64481 p = 1 := by simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2135 p hg
    simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2137 (p : Pattern) (guard : d64483 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64482 p = 1 := by simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2136 p hg
    simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2138 (p : Pattern) (guard : d64484 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64483 p = 1 := by simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2137 p hg
    simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2139 (p : Pattern) (guard : d64485 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64484 p = 1 := by simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2138 p hg
    simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2140 (p : Pattern) (guard : d64486 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64485 p = 1 := by simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2139 p hg
    simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2141 (p : Pattern) (guard : d64487 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64486 p = 1 := by simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2142 (p : Pattern) (guard : d64488 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64487 p = 1 := by simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2141 p hg
    simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2143 (p : Pattern) (guard : d64489 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64488 p = 1 := by simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2142 p hg
    simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2144 (p : Pattern) (guard : d64490 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64489 p = 1 := by simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2143 p hg
    simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2145 (p : Pattern) (guard : d64491 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64490 p = 1 := by simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2144 p hg
    simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2146 (p : Pattern) (guard : d64492 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d64478 p = 1 := by simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64491 p = 1 := by simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2145 p hg
    simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2147 (p : Pattern) (guard : d64493 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 260 with
  | false =>
    have hg : d64492 p = 1 := by simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2146 p hg
    simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2148 (p : Pattern) (guard : d64494 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 259 with
  | false =>
    have hg : d64493 p = 1 := by simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2149 (p : Pattern) (guard : d64495 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 258 with
  | false =>
    have hg : d64494 p = 1 := by simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2148 p hg
    simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2150 (p : Pattern) (guard : d64496 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 257 with
  | false =>
    have hg : d64495 p = 1 := by simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2149 p hg
    simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2151 (p : Pattern) (guard : d64497 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 256 with
  | false =>
    have hg : d64496 p = 1 := by simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2150 p hg
    simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2152 (p : Pattern) (guard : d64498 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 255 with
  | false =>
    have hg : d64497 p = 1 := by simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2153 (p : Pattern) (guard : d64499 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 254 with
  | false =>
    have hg : d64498 p = 1 := by simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2152 p hg
    simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2154 (p : Pattern) (guard : d64500 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 253 with
  | false =>
    have hg : d64499 p = 1 := by simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2153 p hg
    simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2155 (p : Pattern) (guard : d64501 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 252 with
  | false =>
    have hg : d64500 p = 1 := by simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2154 p hg
    simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2156 (p : Pattern) (guard : d64502 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 251 with
  | false =>
    have hg : d64501 p = 1 := by simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2157 (p : Pattern) (guard : d64503 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 250 with
  | false =>
    have hg : d64502 p = 1 := by simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2158 (p : Pattern) (guard : d64504 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 249 with
  | false =>
    have hg : d64503 p = 1 := by simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2157 p hg
    simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2159 (p : Pattern) (guard : d64505 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 245 with
  | false =>
    have hg : d64504 p = 1 := by simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2158 p hg
    simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2160 (p : Pattern) (guard : d64506 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 200 with
  | false =>
    have hg : d64505 p = 1 := by simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2161 (p : Pattern) (guard : d64507 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 199 with
  | false =>
    have hg : d64506 p = 1 := by simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2160 p hg
    simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2162 (p : Pattern) (guard : d64508 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 186 with
  | false =>
    have hg : d64507 p = 1 := by simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2163 (p : Pattern) (guard : d64509 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 185 with
  | false =>
    have hg : d64508 p = 1 := by simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2162 p hg
    simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2164 (p : Pattern) (guard : d64510 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 184 with
  | false =>
    have hg : d64509 p = 1 := by simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2163 p hg
    simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2165 (p : Pattern) (guard : d64511 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 181 with
  | false =>
    have hg : d64510 p = 1 := by simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2166 (p : Pattern) (guard : d64512 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 177 with
  | false =>
    have hg : d64511 p = 1 := by simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2165 p hg
    simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2167 (p : Pattern) (guard : d64513 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 164 with
  | false =>
    have hg : d64512 p = 1 := by simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2166 p hg
    simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2168 (p : Pattern) (guard : d64514 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 156 with
  | false =>
    have hg : d64513 p = 1 := by simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2169 (p : Pattern) (guard : d64515 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 155 with
  | false =>
    have hg : d64514 p = 1 := by simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2170 (p : Pattern) (guard : d64516 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 134 with
  | false =>
    have hg : d64515 p = 1 := by simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2171 (p : Pattern) (guard : d64517 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 133 with
  | false =>
    have hg : d64516 p = 1 := by simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2172 (p : Pattern) (guard : d64518 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 120 with
  | false =>
    have hg : d64517 p = 1 := by simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2173 (p : Pattern) (guard : d64519 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 118 with
  | false =>
    have hg : d64518 p = 1 := by simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2172 p hg
    simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2174 (p : Pattern) (guard : d64520 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 114 with
  | false =>
    have hg : d64519 p = 1 := by simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2173 p hg
    simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2175 (p : Pattern) (guard : d64521 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 111 with
  | false =>
    have hg : d64520 p = 1 := by simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2174 p hg
    simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2176 (p : Pattern) (guard : d64522 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 98 with
  | false =>
    have hg : d64521 p = 1 := by simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2177 (p : Pattern) (guard : d64523 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 97 with
  | false =>
    have hg : d64522 p = 1 := by simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2178 (p : Pattern) (guard : d64524 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 94 with
  | false =>
    have hg : d64523 p = 1 := by simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2177 p hg
    simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2179 (p : Pattern) (guard : d64525 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 76 with
  | false =>
    have hg : d64524 p = 1 := by simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2178 p hg
    simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2180 (p : Pattern) (guard : d64526 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 67 with
  | false =>
    have hg : d64525 p = 1 := by simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2179 p hg
    simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2181 (p : Pattern) (guard : d64527 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 52 with
  | false =>
    have hg : d64526 p = 1 := by simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2180 p hg
    simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2182 (p : Pattern) (guard : d64528 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 47 with
  | false =>
    have hg : d64527 p = 1 := by simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2181 p hg
    simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2183 (p : Pattern) (guard : d64529 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 46 with
  | false =>
    have hg : d64528 p = 1 := by simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2182 p hg
    simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2184 (p : Pattern) (guard : d64530 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 45 with
  | false =>
    have hg : d64529 p = 1 := by simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2183 p hg
    simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2185 (p : Pattern) (guard : d64531 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 30 with
  | false =>
    have hg : d64530 p = 1 := by simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2184 p hg
    simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2186 (p : Pattern) (guard : d64532 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 29 with
  | false =>
    have hg : d64531 p = 1 := by simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2185 p hg
    simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2187 (p : Pattern) (guard : d64533 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 28 with
  | false =>
    have hg : d64532 p = 1 := by simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2188 (p : Pattern) (guard : d64534 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 27 with
  | false =>
    have hg : d64533 p = 1 := by simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2189 (p : Pattern) (guard : d64535 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 25 with
  | false =>
    have hg : d64534 p = 1 := by simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2188 p hg
    simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2190 (p : Pattern) (guard : d53638 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2191 (p : Pattern) (guard : d54864 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53638 p = 1 := by simpa only [d54864, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2190 p hg
    simpa only [d54864, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54864, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d54864, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2192 (p : Pattern) (guard : d54865 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d54864 p = 1 := by simpa only [d54865, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2191 p hg
    simpa only [d54865, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54865, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d54865, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2193 (p : Pattern) (guard : d54866 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54865 p = 1 := by simpa only [d54866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2192 p hg
    simpa only [d54866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2194 (p : Pattern) (guard : d54867 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54866 p = 1 := by simpa only [d54867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2193 p hg
    simpa only [d54867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2195 (p : Pattern) (guard : d54868 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54867 p = 1 := by simpa only [d54868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2194 p hg
    simpa only [d54868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2196 (p : Pattern) (guard : d54869 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54868 p = 1 := by simpa only [d54869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2195 p hg
    simpa only [d54869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2197 (p : Pattern) (guard : d54870 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54869 p = 1 := by simpa only [d54870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d54870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2198 (p : Pattern) (guard : d53654 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2199 (p : Pattern) (guard : d54871 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53654 p = 1 := by simpa only [d54871, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2198 p hg
    simpa only [d54871, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54871, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d54871, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2200 (p : Pattern) (guard : d54872 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d54871 p = 1 := by simpa only [d54872, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d54872, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54872, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d54872, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2201 (p : Pattern) (guard : d54873 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54872 p = 1 := by simpa only [d54873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2200 p hg
    simpa only [d54873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2202 (p : Pattern) (guard : d54874 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54873 p = 1 := by simpa only [d54874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2201 p hg
    simpa only [d54874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2203 (p : Pattern) (guard : d54875 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54874 p = 1 := by simpa only [d54875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2202 p hg
    simpa only [d54875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2204 (p : Pattern) (guard : d54876 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54875 p = 1 := by simpa only [d54876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d54876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2205 (p : Pattern) (guard : d54877 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54876 p = 1 := by simpa only [d54877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2204 p hg
    simpa only [d54877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2206 (p : Pattern) (guard : d54878 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d54870 p = 1 := by simpa only [d54878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2197 p hg
    simpa only [d54878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54877 p = 1 := by simpa only [d54878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d54878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2207 (p : Pattern) (guard : d53679 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2208 (p : Pattern) (guard : d54879 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53679 p = 1 := by simpa only [d54879, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d54879, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54879, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d54879, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2209 (p : Pattern) (guard : d54880 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d54879 p = 1 := by simpa only [d54880, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2208 p hg
    simpa only [d54880, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54880, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d54880, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2210 (p : Pattern) (guard : d54881 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54880 p = 1 := by simpa only [d54881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2209 p hg
    simpa only [d54881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2211 (p : Pattern) (guard : d54882 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54881 p = 1 := by simpa only [d54882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2210 p hg
    simpa only [d54882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2212 (p : Pattern) (guard : d54883 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54882 p = 1 := by simpa only [d54883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2211 p hg
    simpa only [d54883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2213 (p : Pattern) (guard : d54884 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54883 p = 1 := by simpa only [d54884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2212 p hg
    simpa only [d54884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2214 (p : Pattern) (guard : d54885 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54884 p = 1 := by simpa only [d54885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d54885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2215 (p : Pattern) (guard : d54886 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54885 p = 1 := by simpa only [d54886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2214 p hg
    simpa only [d54886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2216 (p : Pattern) (guard : d54887 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d54878 p = 1 := by simpa only [d54887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2206 p hg
    simpa only [d54887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54886 p = 1 := by simpa only [d54887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2215 p hg
    simpa only [d54887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2217 (p : Pattern) (guard : d53706 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2218 (p : Pattern) (guard : d54888 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53706 p = 1 := by simpa only [d54888, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2217 p hg
    simpa only [d54888, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54888, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d54888, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2219 (p : Pattern) (guard : d54889 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d54888 p = 1 := by simpa only [d54889, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2218 p hg
    simpa only [d54889, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54889, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d54889, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2220 (p : Pattern) (guard : d54890 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54889 p = 1 := by simpa only [d54890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2219 p hg
    simpa only [d54890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2221 (p : Pattern) (guard : d54891 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54890 p = 1 := by simpa only [d54891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2220 p hg
    simpa only [d54891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2222 (p : Pattern) (guard : d54892 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54891 p = 1 := by simpa only [d54892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2221 p hg
    simpa only [d54892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2223 (p : Pattern) (guard : d54893 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54892 p = 1 := by simpa only [d54893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2222 p hg
    simpa only [d54893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2224 (p : Pattern) (guard : d54894 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54893 p = 1 := by simpa only [d54894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2223 p hg
    simpa only [d54894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2225 (p : Pattern) (guard : d54895 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54894 p = 1 := by simpa only [d54895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2224 p hg
    simpa only [d54895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2226 (p : Pattern) (guard : d54896 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54895 p = 1 := by simpa only [d54896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2225 p hg
    simpa only [d54896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2227 (p : Pattern) (guard : d54897 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d54887 p = 1 := by simpa only [d54897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2216 p hg
    simpa only [d54897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54896 p = 1 := by simpa only [d54897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2226 p hg
    simpa only [d54897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2228 (p : Pattern) (guard : d53734 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2229 (p : Pattern) (guard : d54898 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53734 p = 1 := by simpa only [d54898, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2228 p hg
    simpa only [d54898, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54898, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d54898, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2230 (p : Pattern) (guard : d54899 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d54898 p = 1 := by simpa only [d54899, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2229 p hg
    simpa only [d54899, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54899, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d54899, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2231 (p : Pattern) (guard : d54900 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54899 p = 1 := by simpa only [d54900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2230 p hg
    simpa only [d54900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2232 (p : Pattern) (guard : d54901 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54900 p = 1 := by simpa only [d54901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d54901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2233 (p : Pattern) (guard : d54902 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54901 p = 1 := by simpa only [d54902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2232 p hg
    simpa only [d54902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2234 (p : Pattern) (guard : d54903 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54902 p = 1 := by simpa only [d54903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2233 p hg
    simpa only [d54903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2235 (p : Pattern) (guard : d54904 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54903 p = 1 := by simpa only [d54904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d54904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2236 (p : Pattern) (guard : d54905 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54904 p = 1 := by simpa only [d54905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2235 p hg
    simpa only [d54905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2237 (p : Pattern) (guard : d54906 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54905 p = 1 := by simpa only [d54906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2236 p hg
    simpa only [d54906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2238 (p : Pattern) (guard : d54907 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54906 p = 1 := by simpa only [d54907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2237 p hg
    simpa only [d54907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2239 (p : Pattern) (guard : d54908 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d54897 p = 1 := by simpa only [d54908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2227 p hg
    simpa only [d54908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54907 p = 1 := by simpa only [d54908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2238 p hg
    simpa only [d54908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2240 (p : Pattern) (guard : d53763 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2241 (p : Pattern) (guard : d54909 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53763 p = 1 := by simpa only [d54909, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d54909, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54909, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d54909, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2242 (p : Pattern) (guard : d54910 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d54909 p = 1 := by simpa only [d54910, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2241 p hg
    simpa only [d54910, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54910, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d54910, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2243 (p : Pattern) (guard : d54911 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54910 p = 1 := by simpa only [d54911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2242 p hg
    simpa only [d54911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2244 (p : Pattern) (guard : d54912 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54911 p = 1 := by simpa only [d54912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2243 p hg
    simpa only [d54912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2245 (p : Pattern) (guard : d54913 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54912 p = 1 := by simpa only [d54913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2244 p hg
    simpa only [d54913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2246 (p : Pattern) (guard : d54914 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54913 p = 1 := by simpa only [d54914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2245 p hg
    simpa only [d54914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2247 (p : Pattern) (guard : d54915 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54914 p = 1 := by simpa only [d54915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2246 p hg
    simpa only [d54915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2248 (p : Pattern) (guard : d54916 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54915 p = 1 := by simpa only [d54916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2247 p hg
    simpa only [d54916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2249 (p : Pattern) (guard : d54917 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54916 p = 1 := by simpa only [d54917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2248 p hg
    simpa only [d54917, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
