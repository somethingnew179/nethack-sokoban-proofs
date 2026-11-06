import NetHack.Soko22Hazard87.Compare032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8250 (p : Pattern) (guard : d228 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d227 p = 1 := by simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8234 p hg
    simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8249 p hg
    simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8251 (p : Pattern) (guard : d229 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d228 p = 1 := by simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8250 p hg
    simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8252 (p : Pattern) (guard : d230 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d229 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8251 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8093 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8253 (p : Pattern) (guard : d231 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d230 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8252 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d70 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8095 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8254 (p : Pattern) (guard : d232 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d231 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8253 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d71 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8096 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8255 (p : Pattern) (guard : d233 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d232 p = 1 := by simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8254 p hg
    simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8256 (p : Pattern) (guard : d234 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d233 p = 1 := by simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8255 p hg
    simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8257 (p : Pattern) (guard : d235 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8256 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d74 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8099 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8258 (p : Pattern) (guard : d236 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d235 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8257 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d75 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8101 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8259 (p : Pattern) (guard : d237 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d236 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8258 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8260 (p : Pattern) (guard : d238 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d237 p = 1 := by simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8259 p hg
    simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8261 (p : Pattern) (guard : d239 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d238 p = 1 := by simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8260 p hg
    simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8262 (p : Pattern) (guard : d240 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d239 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8261 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d79 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8106 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8263 (p : Pattern) (guard : d241 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d240 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8262 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8264 (p : Pattern) (guard : d242 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d241 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8263 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8265 (p : Pattern) (guard : d243 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d242 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8264 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8266 (p : Pattern) (guard : d244 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d243 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8265 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d83 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8110 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8267 (p : Pattern) (guard : d53661 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d244 p = 1 := by simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8266 p hg
    simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8268 (p : Pattern) (guard : d53662 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d53661 p = 1 := by simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8267 p hg
    simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8269 (p : Pattern) (guard : d53663 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53662 p = 1 := by simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8268 p hg
    simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8270 (p : Pattern) (guard : d53664 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53663 p = 1 := by simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8269 p hg
    simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8271 (p : Pattern) (guard : d53665 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53665, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53665, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53664 p = 1 := by simpa only [d53665, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8270 p hg
    simpa only [d53665, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8272 (p : Pattern) (guard : d53666 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53665 p = 1 := by simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8271 p hg
    simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8273 (p : Pattern) (guard : d53667 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53666 p = 1 := by simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8272 p hg
    simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8274 (p : Pattern) (guard : d53668 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53667 p = 1 := by simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8273 p hg
    simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8275 (p : Pattern) (guard : d53669 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53668 p = 1 := by simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8274 p hg
    simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8276 (p : Pattern) (guard : d53670 p = 1) : d47865 p ≤ (-2 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53669 p = 1 := by simpa only [d53670, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8275 p hg
    simpa only [d53670, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53670, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d53670, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8277 (p : Pattern) (guard : d53671 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53660 p = 1 := by simpa only [d53671, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8218 p hg
    simpa only [d53671, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53670 p = 1 := by simpa only [d53671, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8276 p hg
    simpa only [d53671, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8278 (p : Pattern) (guard : d53672 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53671 p = 1 := by simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8277 p hg
    simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8279 (p : Pattern) (guard : d53673 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53672 p = 1 := by simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8278 p hg
    simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8280 (p : Pattern) (guard : d53674 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53673 p = 1 := by simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8279 p hg
    simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8281 (p : Pattern) (guard : d53675 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53674 p = 1 := by simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8280 p hg
    simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8282 (p : Pattern) (guard : d53676 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53675 p = 1 := by simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8281 p hg
    simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8283 (p : Pattern) (guard : d53677 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d53652 p = 1 := by simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8128 p hg
    simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53676 p = 1 := by simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8282 p hg
    simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8284 (p : Pattern) (guard : d307 p = 1) : d4 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare8285 (p : Pattern) (guard : d127 p = 1) : d4 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare8286 (p : Pattern) (guard : d308 p = 1) : d47616 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8285 p hg
    simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8287 (p : Pattern) (guard : d309 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8284 p hg
    simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8286 p hg
    simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8288 (p : Pattern) (guard : d310 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8287 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8132 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8289 (p : Pattern) (guard : d311 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8288 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8133 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8290 (p : Pattern) (guard : d312 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8289 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8134 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8291 (p : Pattern) (guard : d313 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8290 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8292 (p : Pattern) (guard : d314 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8291 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8293 (p : Pattern) (guard : d315 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8292 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8137 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8294 (p : Pattern) (guard : d316 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8293 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8138 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8295 (p : Pattern) (guard : d317 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8294 p hg
    simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8296 (p : Pattern) (guard : d318 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8295 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8140 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8297 (p : Pattern) (guard : d319 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8298 (p : Pattern) (guard : d320 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8297 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8299 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8298 p hg
    simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8300 (p : Pattern) (guard : d322 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8299 p hg
    simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8301 (p : Pattern) (guard : d323 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8300 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8145 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8302 (p : Pattern) (guard : d324 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8301 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d143 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8146 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8303 (p : Pattern) (guard : d325 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8302 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8147 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8304 (p : Pattern) (guard : d326 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325 p = 1 := by simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8303 p hg
    simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8305 (p : Pattern) (guard : d327 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326 p = 1 := by simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8304 p hg
    simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8306 (p : Pattern) (guard : d328 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8305 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8150 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8307 (p : Pattern) (guard : d475 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8150 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8308 (p : Pattern) (guard : d476 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8306 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8307 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8309 (p : Pattern) (guard : d477 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d476 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8308 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8310 (p : Pattern) (guard : d478 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d477 p = 1 := by simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8309 p hg
    simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8311 (p : Pattern) (guard : d479 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d478 p = 1 := by simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8310 p hg
    simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8312 (p : Pattern) (guard : d480 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8307 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8313 (p : Pattern) (guard : d481 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8312 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8314 (p : Pattern) (guard : d482 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8313 p hg
    simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8315 (p : Pattern) (guard : d483 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8314 p hg
    simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8316 (p : Pattern) (guard : d484 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d479 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8311 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8315 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8317 (p : Pattern) (guard : d485 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d484 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8316 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8318 (p : Pattern) (guard : d486 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d485 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8317 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8319 (p : Pattern) (guard : d487 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d486 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8318 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8320 (p : Pattern) (guard : d488 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8315 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8321 (p : Pattern) (guard : d489 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8320 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8322 (p : Pattern) (guard : d490 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8321 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8323 (p : Pattern) (guard : d491 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8322 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8324 (p : Pattern) (guard : d492 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d487 p = 1 := by simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8319 p hg
    simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8323 p hg
    simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8325 (p : Pattern) (guard : d493 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d492 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8324 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8326 (p : Pattern) (guard : d494 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d493 p = 1 := by simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8325 p hg
    simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8327 (p : Pattern) (guard : d495 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d494 p = 1 := by simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8326 p hg
    simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8328 (p : Pattern) (guard : d496 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d495 p = 1 := by simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8327 p hg
    simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8329 (p : Pattern) (guard : d497 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d496 p = 1 := by simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8328 p hg
    simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8330 (p : Pattern) (guard : d500 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d486 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8318 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8331 (p : Pattern) (guard : d501 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8322 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8332 (p : Pattern) (guard : d502 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d500 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8331 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8333 (p : Pattern) (guard : d503 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d502 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8332 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8334 (p : Pattern) (guard : d504 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d503 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8333 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8335 (p : Pattern) (guard : d505 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d504 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8334 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8336 (p : Pattern) (guard : d506 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d505 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8335 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8337 (p : Pattern) (guard : d507 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d496 p = 1 := by simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8328 p hg
    simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d506 p = 1 := by simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8336 p hg
    simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8338 (p : Pattern) (guard : d508 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d497 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8329 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d507 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8337 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8339 (p : Pattern) (guard : d509 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d508 p = 1 := by simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8338 p hg
    simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8340 (p : Pattern) (guard : d53678 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d509 p = 1 := by simpa only [d53678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8339 p hg
    simpa only [d53678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8341 (p : Pattern) (guard : d53679 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53678 p = 1 := by simpa only [d53679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8340 p hg
    simpa only [d53679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8342 (p : Pattern) (guard : d307 p = 1) : d5 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare8343 (p : Pattern) (guard : d127 p = 1) : d5 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare8344 (p : Pattern) (guard : d308 p = 1) : d47705 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8343 p hg
    simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8345 (p : Pattern) (guard : d309 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8342 p hg
    simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8344 p hg
    simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8346 (p : Pattern) (guard : d310 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8345 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8347 (p : Pattern) (guard : d311 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8346 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8181 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8348 (p : Pattern) (guard : d312 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8347 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8349 (p : Pattern) (guard : d313 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8348 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8350 (p : Pattern) (guard : d314 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8349 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8351 (p : Pattern) (guard : d315 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8350 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8185 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8352 (p : Pattern) (guard : d316 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8351 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8186 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8353 (p : Pattern) (guard : d317 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8352 p hg
    simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8354 (p : Pattern) (guard : d318 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8353 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8188 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8355 (p : Pattern) (guard : d319 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8354 p hg
    simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8356 (p : Pattern) (guard : d320 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8355 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8357 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8356 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8358 (p : Pattern) (guard : d322 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8357 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8359 (p : Pattern) (guard : d323 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8358 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8193 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8360 (p : Pattern) (guard : d324 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8359 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d143 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8194 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8361 (p : Pattern) (guard : d325 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8360 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8195 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8362 (p : Pattern) (guard : d326 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325 p = 1 := by simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8361 p hg
    simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8363 (p : Pattern) (guard : d327 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326 p = 1 := by simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8362 p hg
    simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8364 (p : Pattern) (guard : d328 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8363 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8198 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8365 (p : Pattern) (guard : d475 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8198 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8366 (p : Pattern) (guard : d476 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8364 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8365 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8367 (p : Pattern) (guard : d477 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d476 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8366 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8368 (p : Pattern) (guard : d478 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d477 p = 1 := by simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8367 p hg
    simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8369 (p : Pattern) (guard : d479 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d478 p = 1 := by simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8368 p hg
    simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8370 (p : Pattern) (guard : d480 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8365 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8371 (p : Pattern) (guard : d481 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8370 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8372 (p : Pattern) (guard : d482 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8371 p hg
    simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8373 (p : Pattern) (guard : d483 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8372 p hg
    simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8374 (p : Pattern) (guard : d484 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d479 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8369 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8373 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8375 (p : Pattern) (guard : d485 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d484 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8374 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8376 (p : Pattern) (guard : d486 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d485 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8375 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8377 (p : Pattern) (guard : d500 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d486 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8378 (p : Pattern) (guard : d488 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8373 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8379 (p : Pattern) (guard : d489 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8380 (p : Pattern) (guard : d490 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8379 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8381 (p : Pattern) (guard : d501 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8380 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8382 (p : Pattern) (guard : d502 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d500 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8377 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8383 (p : Pattern) (guard : d503 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d502 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8382 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8384 (p : Pattern) (guard : d504 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d503 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8383 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8385 (p : Pattern) (guard : d505 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d504 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8384 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8386 (p : Pattern) (guard : d506 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d505 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8385 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8387 (p : Pattern) (guard : d53680 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53680, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53680, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d506 p = 1 := by simpa only [d53680, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8386 p hg
    simpa only [d53680, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8388 (p : Pattern) (guard : d53681 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53680 p = 1 := by simpa only [d53681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8387 p hg
    simpa only [d53681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8389 (p : Pattern) (guard : d53682 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53681 p = 1 := by simpa only [d53682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8388 p hg
    simpa only [d53682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8390 (p : Pattern) (guard : d53683 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53682 p = 1 := by simpa only [d53683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8389 p hg
    simpa only [d53683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8391 (p : Pattern) (guard : d53684 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53683 p = 1 := by simpa only [d53684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8390 p hg
    simpa only [d53684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8392 (p : Pattern) (guard : d53685 p = 1) : d47768 p ≤ (-2 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53679 p = 1 := by simpa only [d53685, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8341 p hg
    simpa only [d53685, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53684 p = 1 := by simpa only [d53685, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8391 p hg
    simpa only [d53685, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8393 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare8394 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare8395 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8394 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8396 (p : Pattern) (guard : d309 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8393 p hg
    simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8395 p hg
    simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8397 (p : Pattern) (guard : d310 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8396 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8222 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8398 (p : Pattern) (guard : d311 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8223 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8399 (p : Pattern) (guard : d312 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8398 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8224 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8400 (p : Pattern) (guard : d313 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8399 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8401 (p : Pattern) (guard : d314 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8400 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8402 (p : Pattern) (guard : d315 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8401 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8227 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8403 (p : Pattern) (guard : d316 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8402 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8228 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8404 (p : Pattern) (guard : d317 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8405 (p : Pattern) (guard : d318 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8404 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8406 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318 p = 1 := by simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8405 p hg
    simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8407 (p : Pattern) (guard : d319 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8408 (p : Pattern) (guard : d413 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8406 p hg
    simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d319 p = 1 := by simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8407 p hg
    simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8409 (p : Pattern) (guard : d307 p = 1) : d6 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare8410 (p : Pattern) (guard : d127 p = 1) : d6 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare8411 (p : Pattern) (guard : d308 p = 1) : d47633 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8412 (p : Pattern) (guard : d309 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8411 p hg
    simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8413 (p : Pattern) (guard : d310 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8412 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8238 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8414 (p : Pattern) (guard : d311 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8413 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8239 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8415 (p : Pattern) (guard : d312 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8414 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8240 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8416 (p : Pattern) (guard : d313 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8417 (p : Pattern) (guard : d314 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8416 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8418 (p : Pattern) (guard : d315 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8417 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8243 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8419 (p : Pattern) (guard : d316 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8418 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8244 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8420 (p : Pattern) (guard : d317 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8419 p hg
    simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8421 (p : Pattern) (guard : d318 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8420 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8246 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8422 (p : Pattern) (guard : d319 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8421 p hg
    simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8423 (p : Pattern) (guard : d320 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8422 p hg
    simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8424 (p : Pattern) (guard : d414 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d413 p = 1 := by simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8423 p hg
    simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8425 (p : Pattern) (guard : d415 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d414 p = 1 := by simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8424 p hg
    simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8426 (p : Pattern) (guard : d416 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8425 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d229 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8251 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8427 (p : Pattern) (guard : d417 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d416 p = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8426 p hg
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d230 p = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8252 p hg
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8428 (p : Pattern) (guard : d418 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d417 p = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8427 p hg
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d231 p = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8253 p hg
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8429 (p : Pattern) (guard : d419 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d418 p = 1 := by simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8428 p hg
    simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8430 (p : Pattern) (guard : d420 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d419 p = 1 := by simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8429 p hg
    simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8431 (p : Pattern) (guard : d421 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d420 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8430 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d234 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8256 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8432 (p : Pattern) (guard : d673 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8256 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8433 (p : Pattern) (guard : d674 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d421 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8431 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d673 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8434 (p : Pattern) (guard : d675 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d674 p = 1 := by simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8433 p hg
    simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8435 (p : Pattern) (guard : d676 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d675 p = 1 := by simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8434 p hg
    simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8436 (p : Pattern) (guard : d677 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d676 p = 1 := by simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8435 p hg
    simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8437 (p : Pattern) (guard : d682 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d673 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8438 (p : Pattern) (guard : d683 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d682 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8437 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8439 (p : Pattern) (guard : d684 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d683 p = 1 := by simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8438 p hg
    simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8440 (p : Pattern) (guard : d685 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d684 p = 1 := by simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8439 p hg
    simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8441 (p : Pattern) (guard : d686 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d677 p = 1 := by simpa only [d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8436 p hg
    simpa only [d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d685 p = 1 := by simpa only [d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8440 p hg
    simpa only [d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8442 (p : Pattern) (guard : d687 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d686 p = 1 := by simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8441 p hg
    simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8443 (p : Pattern) (guard : d688 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d687 p = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8442 p hg
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8444 (p : Pattern) (guard : d689 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d688 p = 1 := by simpa only [d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8445 (p : Pattern) (guard : d727 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d685 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8440 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8446 (p : Pattern) (guard : d728 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d727 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8445 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8447 (p : Pattern) (guard : d729 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d728 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8446 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8448 (p : Pattern) (guard : d730 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d729 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8447 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8449 (p : Pattern) (guard : d53686 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d689 p = 1 := by simpa only [d53686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8444 p hg
    simpa only [d53686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d730 p = 1 := by simpa only [d53686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8448 p hg
    simpa only [d53686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8450 (p : Pattern) (guard : d53687 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53686 p = 1 := by simpa only [d53687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8449 p hg
    simpa only [d53687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8451 (p : Pattern) (guard : d53688 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d53687 p = 1 := by simpa only [d53688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8450 p hg
    simpa only [d53688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8452 (p : Pattern) (guard : d53689 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53688 p = 1 := by simpa only [d53689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8451 p hg
    simpa only [d53689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8453 (p : Pattern) (guard : d53690 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53689 p = 1 := by simpa only [d53690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8452 p hg
    simpa only [d53690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8454 (p : Pattern) (guard : d53691 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53691, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53691, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53690 p = 1 := by simpa only [d53691, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8453 p hg
    simpa only [d53691, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8455 (p : Pattern) (guard : d53692 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53691 p = 1 := by simpa only [d53692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8454 p hg
    simpa only [d53692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8456 (p : Pattern) (guard : d53693 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53692 p = 1 := by simpa only [d53693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8455 p hg
    simpa only [d53693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8457 (p : Pattern) (guard : d53694 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53693 p = 1 := by simpa only [d53694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8456 p hg
    simpa only [d53694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8458 (p : Pattern) (guard : d53695 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53694 p = 1 := by simpa only [d53695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8457 p hg
    simpa only [d53695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8459 (p : Pattern) (guard : d53696 p = 1) : d47865 p ≤ (-2 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53695 p = 1 := by simpa only [d53696, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8458 p hg
    simpa only [d53696, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53696, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d53696, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8460 (p : Pattern) (guard : d53697 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53685 p = 1 := by simpa only [d53697, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8392 p hg
    simpa only [d53697, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53696 p = 1 := by simpa only [d53697, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8459 p hg
    simpa only [d53697, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8461 (p : Pattern) (guard : d53698 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53697 p = 1 := by simpa only [d53698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8460 p hg
    simpa only [d53698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8462 (p : Pattern) (guard : d53699 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53698 p = 1 := by simpa only [d53699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8461 p hg
    simpa only [d53699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8463 (p : Pattern) (guard : d53700 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53699 p = 1 := by simpa only [d53700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8462 p hg
    simpa only [d53700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8464 (p : Pattern) (guard : d53701 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53700 p = 1 := by simpa only [d53701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8463 p hg
    simpa only [d53701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8465 (p : Pattern) (guard : d53702 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53701 p = 1 := by simpa only [d53702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8464 p hg
    simpa only [d53702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8466 (p : Pattern) (guard : d53703 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53702 p = 1 := by simpa only [d53703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8465 p hg
    simpa only [d53703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8467 (p : Pattern) (guard : d53704 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d53677 p = 1 := by simpa only [d53704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8283 p hg
    simpa only [d53704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53703 p = 1 := by simpa only [d53704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8466 p hg
    simpa only [d53704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8468 (p : Pattern) (guard : d528 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8287 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8469 (p : Pattern) (guard : d529 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8468 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8288 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8470 (p : Pattern) (guard : d530 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8469 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8289 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8471 (p : Pattern) (guard : d531 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8470 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8472 (p : Pattern) (guard : d532 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8471 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8473 (p : Pattern) (guard : d533 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8472 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8292 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8474 (p : Pattern) (guard : d534 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8132 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8475 (p : Pattern) (guard : d535 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8288 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8474 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8476 (p : Pattern) (guard : d536 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8475 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8134 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8477 (p : Pattern) (guard : d537 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8476 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8478 (p : Pattern) (guard : d538 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8477 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8479 (p : Pattern) (guard : d539 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8478 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8137 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8480 (p : Pattern) (guard : d540 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8473 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8479 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8481 (p : Pattern) (guard : d541 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8480 p hg
    simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8482 (p : Pattern) (guard : d542 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8481 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8295 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8483 (p : Pattern) (guard : d543 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8482 p hg
    simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8484 (p : Pattern) (guard : d544 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8483 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8485 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8484 p hg
    simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8486 (p : Pattern) (guard : d546 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8485 p hg
    simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8487 (p : Pattern) (guard : d547 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8486 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8300 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8488 (p : Pattern) (guard : d750 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8140 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8489 (p : Pattern) (guard : d751 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8488 p hg
    simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8490 (p : Pattern) (guard : d752 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8489 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8491 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8490 p hg
    simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8492 (p : Pattern) (guard : d754 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8491 p hg
    simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8493 (p : Pattern) (guard : d755 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8300 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8492 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8494 (p : Pattern) (guard : d756 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8487 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d755 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8493 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8495 (p : Pattern) (guard : d757 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8492 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8496 (p : Pattern) (guard : d758 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8493 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8495 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8497 (p : Pattern) (guard : d759 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d756 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8494 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8496 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8498 (p : Pattern) (guard : d760 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8499 (p : Pattern) (guard : d761 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d760 p = 1 := by simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8498 p hg
    simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
