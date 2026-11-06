import NetHack.Soko22Hazard87.Compare079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20000 (p : Pattern) (guard : d17202 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17201 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19999 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20001 (p : Pattern) (guard : d17203 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17202 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20000 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20002 (p : Pattern) (guard : d17204 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17193 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19994 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17203 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20001 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20003 (p : Pattern) (guard : d17205 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d17194 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19966 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17204 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20002 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20004 (p : Pattern) (guard : d17206 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17205 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20003 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20005 (p : Pattern) (guard : d17207 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d17196 p = 1 := by simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19968 p hg
    simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17206 p = 1 := by simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20004 p hg
    simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20006 (p : Pattern) (guard : d17208 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17182 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19954 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20007 (p : Pattern) (guard : d17209 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17208 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20006 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20008 (p : Pattern) (guard : d17210 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17186 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19958 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20009 (p : Pattern) (guard : d17211 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17210 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20008 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20010 (p : Pattern) (guard : d17212 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17209 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17211 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20009 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20011 (p : Pattern) (guard : d17213 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17212 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20012 (p : Pattern) (guard : d17214 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17213 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20011 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20013 (p : Pattern) (guard : d17215 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17214 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20012 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20014 (p : Pattern) (guard : d17216 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17181 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19953 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20015 (p : Pattern) (guard : d17217 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17216 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20014 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20016 (p : Pattern) (guard : d17218 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17217 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20015 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20017 (p : Pattern) (guard : d17219 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17185 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19957 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20018 (p : Pattern) (guard : d17220 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17219 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20017 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20019 (p : Pattern) (guard : d17221 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17220 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20018 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20020 (p : Pattern) (guard : d17222 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17218 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20016 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17221 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20019 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20021 (p : Pattern) (guard : d17223 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17222 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20020 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20022 (p : Pattern) (guard : d17224 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17223 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20021 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20023 (p : Pattern) (guard : d2143 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare20024 (p : Pattern) (guard : d2144 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20023 p hg
    simpa only [d2144, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d2144, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20025 (p : Pattern) (guard : d2145 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20024 p hg
    simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20026 (p : Pattern) (guard : d2146 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2146, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d2146, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2146, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20025 p hg
    simpa only [d2146, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20027 (p : Pattern) (guard : d2147 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20026 p hg
    simpa only [d2147, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d2147, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20028 (p : Pattern) (guard : d10342 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare20029 (p : Pattern) (guard : d10343 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10342 p = 1 := by simpa only [d10343, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20028 p hg
    simpa only [d10343, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10343, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10343, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20030 (p : Pattern) (guard : d10345 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10343 p = 1 := by simpa only [d10345, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20029 p hg
    simpa only [d10345, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10345, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10345, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20031 (p : Pattern) (guard : d17225 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17225, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d17225, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10345 p = 1 := by simpa only [d17225, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20030 p hg
    simpa only [d17225, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20032 (p : Pattern) (guard : d17226 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20031 p hg
    simpa only [d17226, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d17226, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20033 (p : Pattern) (guard : d17227 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20027 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20032 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20034 (p : Pattern) (guard : d17228 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13676 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20035 (p : Pattern) (guard : d17229 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17227 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20033 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17228 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20034 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20036 (p : Pattern) (guard : d17230 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17229 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20035 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17157 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19900 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20037 (p : Pattern) (guard : d17231 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17231, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d17231, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17230 p = 1 := by simpa only [d17231, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20036 p hg
    simpa only [d17231, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20038 (p : Pattern) (guard : d17232 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17232, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d17232, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17231 p = 1 := by simpa only [d17232, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20037 p hg
    simpa only [d17232, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20039 (p : Pattern) (guard : d17233 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17156 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19899 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19912 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20040 (p : Pattern) (guard : d17234 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19900 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17233 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20039 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20041 (p : Pattern) (guard : d17235 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17235, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d17235, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17234 p = 1 := by simpa only [d17235, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20040 p hg
    simpa only [d17235, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20042 (p : Pattern) (guard : d17236 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17236, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d17236, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17235 p = 1 := by simpa only [d17236, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20041 p hg
    simpa only [d17236, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20043 (p : Pattern) (guard : d17237 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17232 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20038 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17236 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20042 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20044 (p : Pattern) (guard : d17238 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17237 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20043 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17168 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19933 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20045 (p : Pattern) (guard : d17239 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17238 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20044 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20046 (p : Pattern) (guard : d17240 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17239 p = 1 := by simpa only [d17240, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20045 p hg
    simpa only [d17240, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17240, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17240, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20047 (p : Pattern) (guard : d17241 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17241, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d17241, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17240 p = 1 := by simpa only [d17241, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20046 p hg
    simpa only [d17241, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20048 (p : Pattern) (guard : d17242 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17167 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19932 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20049 (p : Pattern) (guard : d17243 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19933 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17242 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20048 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20050 (p : Pattern) (guard : d17244 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17243 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20049 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20051 (p : Pattern) (guard : d17245 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17244 p = 1 := by simpa only [d17245, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20050 p hg
    simpa only [d17245, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17245, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17245, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20052 (p : Pattern) (guard : d17246 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17246, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d17246, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17245 p = 1 := by simpa only [d17246, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d17246, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20053 (p : Pattern) (guard : d17247 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17241 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20047 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17246 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20052 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20054 (p : Pattern) (guard : d17248 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17247 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20053 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20055 (p : Pattern) (guard : d17249 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17248 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20054 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20056 (p : Pattern) (guard : d17250 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17249 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20055 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20057 (p : Pattern) (guard : d17251 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17246 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20052 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20058 (p : Pattern) (guard : d17252 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17251 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20057 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20059 (p : Pattern) (guard : d17253 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17252 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20058 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20060 (p : Pattern) (guard : d17254 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17253 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20059 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20061 (p : Pattern) (guard : d17255 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17250 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20056 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17254 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20060 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20062 (p : Pattern) (guard : d128396 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17255 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20061 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20063 (p : Pattern) (guard : d13614 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20064 (p : Pattern) (guard : d17294 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19913 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13614 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20063 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20065 (p : Pattern) (guard : d17295 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17295, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d17295, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17294 p = 1 := by simpa only [d17295, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20064 p hg
    simpa only [d17295, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20066 (p : Pattern) (guard : d17296 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17296, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d17296, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17295 p = 1 := by simpa only [d17296, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20065 p hg
    simpa only [d17296, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20067 (p : Pattern) (guard : d17297 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17296 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20066 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20068 (p : Pattern) (guard : d17298 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19933 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17297 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20067 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20069 (p : Pattern) (guard : d17299 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17298 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20068 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20070 (p : Pattern) (guard : d17300 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17299 p = 1 := by simpa only [d17300, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20069 p hg
    simpa only [d17300, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17300, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17300, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20071 (p : Pattern) (guard : d17301 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17301, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d17301, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17300 p = 1 := by simpa only [d17301, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20070 p hg
    simpa only [d17301, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20072 (p : Pattern) (guard : d17302 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17301 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20071 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20073 (p : Pattern) (guard : d17303 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17302 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20072 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20074 (p : Pattern) (guard : d17304 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17303 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20073 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20075 (p : Pattern) (guard : d17305 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17304 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20074 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20076 (p : Pattern) (guard : d17306 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17305 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20075 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20077 (p : Pattern) (guard : d17307 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17306 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20076 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20078 (p : Pattern) (guard : d128397 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128396 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20062 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17307 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20077 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20079 (p : Pattern) (guard : d128398 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d17224 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20022 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128397 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20078 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20080 (p : Pattern) (guard : d128399 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d17215 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20013 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128398 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20079 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20081 (p : Pattern) (guard : d128400 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128399 p = 1 := by simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20080 p hg
    simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20082 (p : Pattern) (guard : d17208 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17182 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19983 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20083 (p : Pattern) (guard : d17209 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17208 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20082 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20084 (p : Pattern) (guard : d17210 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17186 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19987 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20085 (p : Pattern) (guard : d17211 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17210 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20084 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20086 (p : Pattern) (guard : d17212 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17209 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20083 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17211 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20085 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20087 (p : Pattern) (guard : d17213 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17212 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20086 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20088 (p : Pattern) (guard : d17214 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17213 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20087 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20089 (p : Pattern) (guard : d17215 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17214 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20088 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20090 (p : Pattern) (guard : d17216 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17181 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19982 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20091 (p : Pattern) (guard : d17217 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17216 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20090 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20092 (p : Pattern) (guard : d17218 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17217 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20091 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20093 (p : Pattern) (guard : d17219 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17185 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19986 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20094 (p : Pattern) (guard : d17220 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17219 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20093 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20095 (p : Pattern) (guard : d17221 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17220 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20094 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20096 (p : Pattern) (guard : d17222 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17218 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20092 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17221 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20095 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20097 (p : Pattern) (guard : d17223 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17222 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20096 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20098 (p : Pattern) (guard : d17224 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17223 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20097 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20099 (p : Pattern) (guard : d17232 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17232, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d17232, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17231 p = 1 := by simpa only [d17232, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20037 p hg
    simpa only [d17232, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20100 (p : Pattern) (guard : d17236 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17236, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d17236, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17235 p = 1 := by simpa only [d17236, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20041 p hg
    simpa only [d17236, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20101 (p : Pattern) (guard : d17237 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17232 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20099 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17236 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20100 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20102 (p : Pattern) (guard : d17238 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17237 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20101 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17168 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19971 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20103 (p : Pattern) (guard : d17239 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17238 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20102 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20104 (p : Pattern) (guard : d17240 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17239 p = 1 := by simpa only [d17240, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20103 p hg
    simpa only [d17240, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17240, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17240, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20105 (p : Pattern) (guard : d17241 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17241, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d17241, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17240 p = 1 := by simpa only [d17241, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20104 p hg
    simpa only [d17241, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20106 (p : Pattern) (guard : d17242 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17167 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19970 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20107 (p : Pattern) (guard : d17243 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19971 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17242 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20106 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20108 (p : Pattern) (guard : d17244 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17243 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20107 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20109 (p : Pattern) (guard : d17245 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17244 p = 1 := by simpa only [d17245, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20108 p hg
    simpa only [d17245, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17245, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17245, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20110 (p : Pattern) (guard : d17246 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17246, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d17246, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17245 p = 1 := by simpa only [d17246, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20109 p hg
    simpa only [d17246, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20111 (p : Pattern) (guard : d17247 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17241 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20105 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17246 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20110 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20112 (p : Pattern) (guard : d17248 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17247 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20111 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20113 (p : Pattern) (guard : d17249 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17248 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20112 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20114 (p : Pattern) (guard : d17250 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17249 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20113 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20115 (p : Pattern) (guard : d17251 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17246 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20110 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19981 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20116 (p : Pattern) (guard : d17252 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17251 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20115 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20117 (p : Pattern) (guard : d17253 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17252 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20116 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20118 (p : Pattern) (guard : d17254 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17253 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20117 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20119 (p : Pattern) (guard : d17255 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17250 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20114 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17254 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20118 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20120 (p : Pattern) (guard : d128396 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17255 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20119 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20121 (p : Pattern) (guard : d17296 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17296, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d17296, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17295 p = 1 := by simpa only [d17296, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20065 p hg
    simpa only [d17296, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20122 (p : Pattern) (guard : d17297 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17296 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20121 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20123 (p : Pattern) (guard : d17298 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19971 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17297 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20122 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20124 (p : Pattern) (guard : d17299 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17298 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20123 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20125 (p : Pattern) (guard : d17300 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17299 p = 1 := by simpa only [d17300, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20124 p hg
    simpa only [d17300, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17300, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17300, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20126 (p : Pattern) (guard : d17301 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17301, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d17301, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17300 p = 1 := by simpa only [d17301, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20125 p hg
    simpa only [d17301, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20127 (p : Pattern) (guard : d17302 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17301 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20126 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20128 (p : Pattern) (guard : d17303 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17302 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20127 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20129 (p : Pattern) (guard : d17304 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17303 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20128 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20130 (p : Pattern) (guard : d17305 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17304 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20129 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20131 (p : Pattern) (guard : d17306 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17305 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20130 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20132 (p : Pattern) (guard : d17307 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17306 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20131 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20133 (p : Pattern) (guard : d128397 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128396 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20120 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17307 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20132 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20134 (p : Pattern) (guard : d128398 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d17224 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20098 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128397 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20133 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20135 (p : Pattern) (guard : d128399 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d17215 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20089 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128398 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20136 (p : Pattern) (guard : d17312 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17208 p = 1 := by simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20006 p hg
    simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20137 (p : Pattern) (guard : d17313 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17210 p = 1 := by simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20008 p hg
    simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20138 (p : Pattern) (guard : d17314 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17312 p = 1 := by simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20136 p hg
    simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17313 p = 1 := by simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20137 p hg
    simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20139 (p : Pattern) (guard : d17315 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17314 p = 1 := by simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20138 p hg
    simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20140 (p : Pattern) (guard : d17316 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17315 p = 1 := by simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20139 p hg
    simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20141 (p : Pattern) (guard : d17317 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17316 p = 1 := by simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20142 (p : Pattern) (guard : d17318 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17217 p = 1 := by simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20015 p hg
    simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20143 (p : Pattern) (guard : d17319 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17220 p = 1 := by simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20018 p hg
    simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20144 (p : Pattern) (guard : d17320 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17318 p = 1 := by simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20142 p hg
    simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17319 p = 1 := by simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20143 p hg
    simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20145 (p : Pattern) (guard : d17321 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17320 p = 1 := by simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20144 p hg
    simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20146 (p : Pattern) (guard : d17322 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17321 p = 1 := by simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20145 p hg
    simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20147 (p : Pattern) (guard : d17323 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17249 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20055 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20148 (p : Pattern) (guard : d17324 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17253 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20059 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20149 (p : Pattern) (guard : d17325 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17323 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20147 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17324 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20148 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20150 (p : Pattern) (guard : d128401 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17325 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20149 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20151 (p : Pattern) (guard : d17330 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17304 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20074 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20152 (p : Pattern) (guard : d17331 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17330 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20151 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20153 (p : Pattern) (guard : d17332 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17331 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20152 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20154 (p : Pattern) (guard : d128402 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128401 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20150 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17332 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20153 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20155 (p : Pattern) (guard : d128403 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d17322 p = 1 := by simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20146 p hg
    simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128402 p = 1 := by simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20154 p hg
    simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20156 (p : Pattern) (guard : d128404 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d17317 p = 1 := by simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20141 p hg
    simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128403 p = 1 := by simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20155 p hg
    simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20157 (p : Pattern) (guard : d128405 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128399 p = 1 := by simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128404 p = 1 := by simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20156 p hg
    simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20158 (p : Pattern) (guard : d128406 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128400 p = 1 := by simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20081 p hg
    simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128405 p = 1 := by simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20157 p hg
    simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20159 (p : Pattern) (guard : d17338 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17254 p = 1 := by simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20118 p hg
    simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19989 p hg
    simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20160 (p : Pattern) (guard : d17339 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17338 p = 1 := by simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20159 p hg
    simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20161 (p : Pattern) (guard : d17340 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17339 p = 1 := by simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20160 p hg
    simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20162 (p : Pattern) (guard : d17341 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17340 p = 1 := by simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20161 p hg
    simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20163 (p : Pattern) (guard : d17342 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17341 p = 1 := by simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20162 p hg
    simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20164 (p : Pattern) (guard : d17343 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17188 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19960 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20165 (p : Pattern) (guard : d17344 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17343 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20166 (p : Pattern) (guard : d17345 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17344 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20167 (p : Pattern) (guard : d17346 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17345 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20166 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20168 (p : Pattern) (guard : d17347 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17346 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20169 (p : Pattern) (guard : d17348 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17342 p = 1 := by simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20163 p hg
    simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17347 p = 1 := by simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20168 p hg
    simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20170 (p : Pattern) (guard : d17343 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17188 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19989 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20171 (p : Pattern) (guard : d17344 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17343 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20172 (p : Pattern) (guard : d17345 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17344 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20171 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20173 (p : Pattern) (guard : d17346 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17345 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20172 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20174 (p : Pattern) (guard : d17347 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17346 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20173 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20175 (p : Pattern) (guard : d17349 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17198 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20176 (p : Pattern) (guard : d17350 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17349 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20175 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20177 (p : Pattern) (guard : d17351 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17350 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20176 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20178 (p : Pattern) (guard : d17352 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17351 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20177 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20179 (p : Pattern) (guard : d17353 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17352 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20178 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20180 (p : Pattern) (guard : d17354 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17347 p = 1 := by simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20174 p hg
    simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17353 p = 1 := by simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20179 p hg
    simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20181 (p : Pattern) (guard : d17355 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d17348 p = 1 := by simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20169 p hg
    simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17354 p = 1 := by simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20180 p hg
    simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20182 (p : Pattern) (guard : d128407 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128406 p = 1 := by simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20158 p hg
    simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17355 p = 1 := by simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20181 p hg
    simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20183 (p : Pattern) (guard : d128408 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128407 p = 1 := by simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20182 p hg
    simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20184 (p : Pattern) (guard : d128409 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d17207 p = 1 := by simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20005 p hg
    simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128408 p = 1 := by simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20183 p hg
    simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20185 (p : Pattern) (guard : d2143 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20186 (p : Pattern) (guard : d2144 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20185 p hg
    simpa only [d2144, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d2144, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20187 (p : Pattern) (guard : d2145 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20186 p hg
    simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20188 (p : Pattern) (guard : d2146 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20187 p hg
    simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20189 (p : Pattern) (guard : d2147 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20188 p hg
    simpa only [d2147, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d2147, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20190 (p : Pattern) (guard : d10342 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20191 (p : Pattern) (guard : d10343 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10342 p = 1 := by simpa only [d10343, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20190 p hg
    simpa only [d10343, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10343, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10343, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20192 (p : Pattern) (guard : d10345 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10343 p = 1 := by simpa only [d10345, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20191 p hg
    simpa only [d10345, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10345, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10345, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20193 (p : Pattern) (guard : d17225 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17225, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d17225, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10345 p = 1 := by simpa only [d17225, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20192 p hg
    simpa only [d17225, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20194 (p : Pattern) (guard : d17226 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20193 p hg
    simpa only [d17226, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d17226, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20195 (p : Pattern) (guard : d17227 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20189 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20194 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20196 (p : Pattern) (guard : d10352 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20197 (p : Pattern) (guard : d10353 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20198 (p : Pattern) (guard : d10355 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20199 (p : Pattern) (guard : d13675 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20198 p hg
    simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20200 (p : Pattern) (guard : d13676 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20201 (p : Pattern) (guard : d17228 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13676 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20200 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20202 (p : Pattern) (guard : d17229 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17227 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20195 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17228 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20201 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20203 (p : Pattern) (guard : d2034 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20204 (p : Pattern) (guard : d2035 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20203 p hg
    simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20205 (p : Pattern) (guard : d2036 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20204 p hg
    simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20206 (p : Pattern) (guard : d2037 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20205 p hg
    simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20207 (p : Pattern) (guard : d2038 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20206 p hg
    simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20208 (p : Pattern) (guard : d10363 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20209 (p : Pattern) (guard : d10364 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20208 p hg
    simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20210 (p : Pattern) (guard : d10366 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20211 (p : Pattern) (guard : d17153 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20210 p hg
    simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20212 (p : Pattern) (guard : d17154 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20211 p hg
    simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20213 (p : Pattern) (guard : d17155 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20207 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20212 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20214 (p : Pattern) (guard : d10370 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20215 (p : Pattern) (guard : d10371 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20214 p hg
    simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20216 (p : Pattern) (guard : d10373 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20215 p hg
    simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20217 (p : Pattern) (guard : d15548 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20216 p hg
    simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20218 (p : Pattern) (guard : d15549 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20217 p hg
    simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20219 (p : Pattern) (guard : d17156 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20200 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20218 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20220 (p : Pattern) (guard : d17157 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20213 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20219 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20221 (p : Pattern) (guard : d17230 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17229 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20202 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17157 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20220 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20222 (p : Pattern) (guard : d17231 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17231, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d17231, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17230 p = 1 := by simpa only [d17231, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20221 p hg
    simpa only [d17231, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20223 (p : Pattern) (guard : d17232 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17232, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d17232, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17231 p = 1 := by simpa only [d17232, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20222 p hg
    simpa only [d17232, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20224 (p : Pattern) (guard : d15550 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20218 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20225 (p : Pattern) (guard : d17233 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17156 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20219 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20224 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20226 (p : Pattern) (guard : d17234 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20220 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17233 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20225 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20227 (p : Pattern) (guard : d17235 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17235, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d17235, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17234 p = 1 := by simpa only [d17235, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20226 p hg
    simpa only [d17235, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20228 (p : Pattern) (guard : d17236 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17236, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d17236, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17235 p = 1 := by simpa only [d17236, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20227 p hg
    simpa only [d17236, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20229 (p : Pattern) (guard : d17237 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17232 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20223 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17236 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20228 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20230 (p : Pattern) (guard : d2052 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20231 (p : Pattern) (guard : d2053 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20230 p hg
    simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20232 (p : Pattern) (guard : d2054 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20231 p hg
    simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20233 (p : Pattern) (guard : d2055 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20232 p hg
    simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20234 (p : Pattern) (guard : d2056 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20233 p hg
    simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20235 (p : Pattern) (guard : d10390 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20236 (p : Pattern) (guard : d10391 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20235 p hg
    simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20237 (p : Pattern) (guard : d10393 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20236 p hg
    simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20238 (p : Pattern) (guard : d17158 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20237 p hg
    simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20239 (p : Pattern) (guard : d17159 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20240 (p : Pattern) (guard : d17160 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20234 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20239 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20241 (p : Pattern) (guard : d17161 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20240 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20224 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20242 (p : Pattern) (guard : d17162 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20220 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20241 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20243 (p : Pattern) (guard : d17163 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20242 p hg
    simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20244 (p : Pattern) (guard : d17164 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20243 p hg
    simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20245 (p : Pattern) (guard : d5246 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20246 (p : Pattern) (guard : d5247 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20245 p hg
    simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20247 (p : Pattern) (guard : d5248 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20246 p hg
    simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20248 (p : Pattern) (guard : d5249 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20247 p hg
    simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20249 (p : Pattern) (guard : d5250 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20248 p hg
    simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
