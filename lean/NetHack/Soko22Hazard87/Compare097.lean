import NetHack.Soko22Hazard87.Compare096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24250 (p : Pattern) (guard : d659 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24251 (p : Pattern) (guard : d18708 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d659 p = 1 := by simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24250 p hg
    simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24252 (p : Pattern) (guard : d181023 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18708 p = 1 := by simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24251 p hg
    simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24253 (p : Pattern) (guard : d181024 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181023 p = 1 := by simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24252 p hg
    simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24254 (p : Pattern) (guard : d16156 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24255 (p : Pattern) (guard : d18711 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d16156 p = 1 := by simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24254 p hg
    simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24256 (p : Pattern) (guard : d181025 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18711 p = 1 := by simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24255 p hg
    simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24257 (p : Pattern) (guard : d181026 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181025 p = 1 := by simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24256 p hg
    simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24258 (p : Pattern) (guard : d181027 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181024 p = 1 := by simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24253 p hg
    simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181026 p = 1 := by simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24257 p hg
    simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24259 (p : Pattern) (guard : d12858 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24260 (p : Pattern) (guard : d18715 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d12858 p = 1 := by simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24259 p hg
    simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24261 (p : Pattern) (guard : d181028 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18715 p = 1 := by simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24260 p hg
    simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24262 (p : Pattern) (guard : d181029 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181028 p = 1 := by simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24261 p hg
    simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24263 (p : Pattern) (guard : d181030 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181029 p = 1 := by simpa only [d181030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24262 p hg
    simpa only [d181030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180978 p = 1 := by simpa only [d181030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24205 p hg
    simpa only [d181030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24264 (p : Pattern) (guard : d181031 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181027 p = 1 := by simpa only [d181031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24258 p hg
    simpa only [d181031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181030 p = 1 := by simpa only [d181031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24263 p hg
    simpa only [d181031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24265 (p : Pattern) (guard : d181032 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181031 p = 1 := by simpa only [d181032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24264 p hg
    simpa only [d181032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180980 p = 1 := by simpa only [d181032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24207 p hg
    simpa only [d181032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24266 (p : Pattern) (guard : d181033 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181033, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181033, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181032 p = 1 := by simpa only [d181033, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24265 p hg
    simpa only [d181033, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24267 (p : Pattern) (guard : d181034 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181034, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181034, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181033 p = 1 := by simpa only [d181034, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24266 p hg
    simpa only [d181034, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24268 (p : Pattern) (guard : d181035 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180979 p = 1 := by simpa only [d181035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24206 p hg
    simpa only [d181035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180911 p = 1 := by simpa only [d181035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24129 p hg
    simpa only [d181035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24269 (p : Pattern) (guard : d181036 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180980 p = 1 := by simpa only [d181036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24207 p hg
    simpa only [d181036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181035 p = 1 := by simpa only [d181036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24268 p hg
    simpa only [d181036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24270 (p : Pattern) (guard : d181037 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181037, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181037, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181036 p = 1 := by simpa only [d181037, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24269 p hg
    simpa only [d181037, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24271 (p : Pattern) (guard : d181038 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181038, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181038, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181037 p = 1 := by simpa only [d181038, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24270 p hg
    simpa only [d181038, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24272 (p : Pattern) (guard : d181039 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181034 p = 1 := by simpa only [d181039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24267 p hg
    simpa only [d181039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181038 p = 1 := by simpa only [d181039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24271 p hg
    simpa only [d181039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24273 (p : Pattern) (guard : d181040 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181039 p = 1 := by simpa only [d181040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24272 p hg
    simpa only [d181040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180984 p = 1 := by simpa only [d181040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24211 p hg
    simpa only [d181040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24274 (p : Pattern) (guard : d181041 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181040 p = 1 := by simpa only [d181041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24273 p hg
    simpa only [d181041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24275 (p : Pattern) (guard : d181042 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181041 p = 1 := by simpa only [d181042, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24274 p hg
    simpa only [d181042, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181042, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181042, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24276 (p : Pattern) (guard : d181043 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181043, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181043, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181042 p = 1 := by simpa only [d181043, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24275 p hg
    simpa only [d181043, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24277 (p : Pattern) (guard : d181044 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180947 p = 1 := by simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24170 p hg
    simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24278 (p : Pattern) (guard : d181045 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180984 p = 1 := by simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24211 p hg
    simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181044 p = 1 := by simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24277 p hg
    simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24279 (p : Pattern) (guard : d181046 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181045 p = 1 := by simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24278 p hg
    simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24280 (p : Pattern) (guard : d181047 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181046 p = 1 := by simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24279 p hg
    simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24281 (p : Pattern) (guard : d181048 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181047 p = 1 := by simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24280 p hg
    simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24282 (p : Pattern) (guard : d181049 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181043 p = 1 := by simpa only [d181049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24276 p hg
    simpa only [d181049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181048 p = 1 := by simpa only [d181049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24281 p hg
    simpa only [d181049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24283 (p : Pattern) (guard : d181050 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181049 p = 1 := by simpa only [d181050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24282 p hg
    simpa only [d181050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24284 (p : Pattern) (guard : d181051 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181050 p = 1 := by simpa only [d181051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24283 p hg
    simpa only [d181051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24285 (p : Pattern) (guard : d181052 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181051 p = 1 := by simpa only [d181052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24284 p hg
    simpa only [d181052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24286 (p : Pattern) (guard : d181053 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181044 p = 1 := by simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24277 p hg
    simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24287 (p : Pattern) (guard : d181054 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181053 p = 1 := by simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24286 p hg
    simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24288 (p : Pattern) (guard : d181055 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181054 p = 1 := by simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24287 p hg
    simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24289 (p : Pattern) (guard : d181056 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181055 p = 1 := by simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24288 p hg
    simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24290 (p : Pattern) (guard : d181057 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181048 p = 1 := by simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24281 p hg
    simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181056 p = 1 := by simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24289 p hg
    simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24291 (p : Pattern) (guard : d181058 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181057 p = 1 := by simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24290 p hg
    simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24292 (p : Pattern) (guard : d181059 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181058 p = 1 := by simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24291 p hg
    simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24293 (p : Pattern) (guard : d181060 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181059 p = 1 := by simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24292 p hg
    simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24294 (p : Pattern) (guard : d181061 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181052 p = 1 := by simpa only [d181061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24285 p hg
    simpa only [d181061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181060 p = 1 := by simpa only [d181061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24293 p hg
    simpa only [d181061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24295 (p : Pattern) (guard : d181062 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181061 p = 1 := by simpa only [d181062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24294 p hg
    simpa only [d181062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24296 (p : Pattern) (guard : d181063 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181048 p = 1 := by simpa only [d181063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24281 p hg
    simpa only [d181063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24297 (p : Pattern) (guard : d181064 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181063 p = 1 := by simpa only [d181064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24296 p hg
    simpa only [d181064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24298 (p : Pattern) (guard : d181065 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181064 p = 1 := by simpa only [d181065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24297 p hg
    simpa only [d181065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24299 (p : Pattern) (guard : d181066 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181065 p = 1 := by simpa only [d181066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24298 p hg
    simpa only [d181066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24300 (p : Pattern) (guard : d181067 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181066 p = 1 := by simpa only [d181067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24299 p hg
    simpa only [d181067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24301 (p : Pattern) (guard : d181068 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181067 p = 1 := by simpa only [d181068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24300 p hg
    simpa only [d181068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24302 (p : Pattern) (guard : d181069 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181062 p = 1 := by simpa only [d181069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24295 p hg
    simpa only [d181069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181068 p = 1 := by simpa only [d181069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24301 p hg
    simpa only [d181069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24303 (p : Pattern) (guard : d181070 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181069 p = 1 := by simpa only [d181070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d181070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24304 (p : Pattern) (guard : d181071 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181070 p = 1 := by simpa only [d181071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24303 p hg
    simpa only [d181071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24305 (p : Pattern) (guard : d181072 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181072, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181072, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181071 p = 1 := by simpa only [d181072, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24304 p hg
    simpa only [d181072, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24306 (p : Pattern) (guard : d181073 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181072 p = 1 := by simpa only [d181073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24305 p hg
    simpa only [d181073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24307 (p : Pattern) (guard : d181074 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181056 p = 1 := by simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24289 p hg
    simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24308 (p : Pattern) (guard : d181075 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181074 p = 1 := by simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24307 p hg
    simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24309 (p : Pattern) (guard : d181076 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181075 p = 1 := by simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24308 p hg
    simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24310 (p : Pattern) (guard : d181077 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181076 p = 1 := by simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24309 p hg
    simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24311 (p : Pattern) (guard : d181078 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181077 p = 1 := by simpa only [d181078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24310 p hg
    simpa only [d181078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24312 (p : Pattern) (guard : d181079 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181078 p = 1 := by simpa only [d181079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24311 p hg
    simpa only [d181079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24313 (p : Pattern) (guard : d181080 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181079 p = 1 := by simpa only [d181080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24312 p hg
    simpa only [d181080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24314 (p : Pattern) (guard : d181081 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181080 p = 1 := by simpa only [d181081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24313 p hg
    simpa only [d181081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24315 (p : Pattern) (guard : d181082 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181081 p = 1 := by simpa only [d181082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24314 p hg
    simpa only [d181082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24316 (p : Pattern) (guard : d181083 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181083, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181083, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181082 p = 1 := by simpa only [d181083, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24315 p hg
    simpa only [d181083, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24317 (p : Pattern) (guard : d181084 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181083 p = 1 := by simpa only [d181084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24316 p hg
    simpa only [d181084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24318 (p : Pattern) (guard : d181085 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181073 p = 1 := by simpa only [d181085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24306 p hg
    simpa only [d181085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181084 p = 1 := by simpa only [d181085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24317 p hg
    simpa only [d181085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24319 (p : Pattern) (guard : d181086 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181085 p = 1 := by simpa only [d181086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24318 p hg
    simpa only [d181086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24320 (p : Pattern) (guard : d181087 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181086 p = 1 := by simpa only [d181087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24319 p hg
    simpa only [d181087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24321 (p : Pattern) (guard : d181088 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181087 p = 1 := by simpa only [d181088, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24320 p hg
    simpa only [d181088, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181088, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d181088, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24322 (p : Pattern) (guard : d181089 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181089, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d181089, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181088 p = 1 := by simpa only [d181089, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24321 p hg
    simpa only [d181089, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24323 (p : Pattern) (guard : d181090 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181089 p = 1 := by simpa only [d181090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24322 p hg
    simpa only [d181090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24324 (p : Pattern) (guard : d181091 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181090 p = 1 := by simpa only [d181091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24323 p hg
    simpa only [d181091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24325 (p : Pattern) (guard : d181092 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181091 p = 1 := by simpa only [d181092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24324 p hg
    simpa only [d181092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24326 (p : Pattern) (guard : d181093 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181092 p = 1 := by simpa only [d181093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24325 p hg
    simpa only [d181093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24327 (p : Pattern) (guard : d181094 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181093 p = 1 := by simpa only [d181094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24326 p hg
    simpa only [d181094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24328 (p : Pattern) (guard : d181095 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181094 p = 1 := by simpa only [d181095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24327 p hg
    simpa only [d181095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24329 (p : Pattern) (guard : d181096 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d181022 p = 1 := by simpa only [d181096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24249 p hg
    simpa only [d181096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181095 p = 1 := by simpa only [d181096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24328 p hg
    simpa only [d181096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24330 (p : Pattern) (guard : d965 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24331 (p : Pattern) (guard : d18831 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d965 p = 1 := by simpa only [d18831, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24330 p hg
    simpa only [d18831, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18831, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18831, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24332 (p : Pattern) (guard : d181097 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18831 p = 1 := by simpa only [d181097, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24331 p hg
    simpa only [d181097, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181097, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181097, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24333 (p : Pattern) (guard : d181098 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181097 p = 1 := by simpa only [d181098, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24332 p hg
    simpa only [d181098, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181098, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181098, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24334 (p : Pattern) (guard : d16356 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24335 (p : Pattern) (guard : d18834 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d16356 p = 1 := by simpa only [d18834, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24334 p hg
    simpa only [d18834, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18834, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18834, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24336 (p : Pattern) (guard : d181099 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18834 p = 1 := by simpa only [d181099, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24335 p hg
    simpa only [d181099, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181099, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181099, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24337 (p : Pattern) (guard : d181100 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181099 p = 1 := by simpa only [d181100, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24336 p hg
    simpa only [d181100, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181100, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181100, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24338 (p : Pattern) (guard : d181101 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181098 p = 1 := by simpa only [d181101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24333 p hg
    simpa only [d181101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181100 p = 1 := by simpa only [d181101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24337 p hg
    simpa only [d181101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24339 (p : Pattern) (guard : d14644 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24340 (p : Pattern) (guard : d18838 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d14644 p = 1 := by simpa only [d18838, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24339 p hg
    simpa only [d18838, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18838, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18838, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24341 (p : Pattern) (guard : d181102 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18838 p = 1 := by simpa only [d181102, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24340 p hg
    simpa only [d181102, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181102, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181102, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24342 (p : Pattern) (guard : d181103 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181102 p = 1 := by simpa only [d181103, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24341 p hg
    simpa only [d181103, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181103, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181103, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24343 (p : Pattern) (guard : d181104 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181103 p = 1 := by simpa only [d181104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24342 p hg
    simpa only [d181104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181029 p = 1 := by simpa only [d181104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24262 p hg
    simpa only [d181104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24344 (p : Pattern) (guard : d181105 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181101 p = 1 := by simpa only [d181105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24338 p hg
    simpa only [d181105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181104 p = 1 := by simpa only [d181105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24343 p hg
    simpa only [d181105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24345 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24346 (p : Pattern) (guard : d18843 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24345 p hg
    simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24347 (p : Pattern) (guard : d181106 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18843 p = 1 := by simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24346 p hg
    simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24348 (p : Pattern) (guard : d181107 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181106 p = 1 := by simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24347 p hg
    simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24349 (p : Pattern) (guard : d181108 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181029 p = 1 := by simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24262 p hg
    simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181107 p = 1 := by simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24350 (p : Pattern) (guard : d181109 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181027 p = 1 := by simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24258 p hg
    simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181108 p = 1 := by simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24349 p hg
    simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24351 (p : Pattern) (guard : d181110 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181105 p = 1 := by simpa only [d181110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24344 p hg
    simpa only [d181110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181109 p = 1 := by simpa only [d181110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24350 p hg
    simpa only [d181110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24352 (p : Pattern) (guard : d181111 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181111, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181111, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181110 p = 1 := by simpa only [d181111, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24351 p hg
    simpa only [d181111, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24353 (p : Pattern) (guard : d181112 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181112, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181112, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181111 p = 1 := by simpa only [d181112, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24352 p hg
    simpa only [d181112, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24354 (p : Pattern) (guard : d181113 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181107 p = 1 := by simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24355 (p : Pattern) (guard : d181114 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181108 p = 1 := by simpa only [d181114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24349 p hg
    simpa only [d181114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181113 p = 1 := by simpa only [d181114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24354 p hg
    simpa only [d181114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24356 (p : Pattern) (guard : d181115 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181109 p = 1 := by simpa only [d181115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24350 p hg
    simpa only [d181115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181114 p = 1 := by simpa only [d181115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24355 p hg
    simpa only [d181115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24357 (p : Pattern) (guard : d181116 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181116, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181116, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181115 p = 1 := by simpa only [d181116, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24356 p hg
    simpa only [d181116, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24358 (p : Pattern) (guard : d181117 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181117, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181117, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181116 p = 1 := by simpa only [d181117, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24357 p hg
    simpa only [d181117, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24359 (p : Pattern) (guard : d181118 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181112 p = 1 := by simpa only [d181118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24353 p hg
    simpa only [d181118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181117 p = 1 := by simpa only [d181118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24358 p hg
    simpa only [d181118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24360 (p : Pattern) (guard : d181119 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180975 p = 1 := by simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24200 p hg
    simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181107 p = 1 := by simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24361 (p : Pattern) (guard : d181120 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181119 p = 1 := by simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24360 p hg
    simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181113 p = 1 := by simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24354 p hg
    simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24362 (p : Pattern) (guard : d181121 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181109 p = 1 := by simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24350 p hg
    simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181120 p = 1 := by simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24361 p hg
    simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24363 (p : Pattern) (guard : d181122 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181121 p = 1 := by simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24362 p hg
    simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24364 (p : Pattern) (guard : d181123 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181122 p = 1 := by simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24363 p hg
    simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24365 (p : Pattern) (guard : d181124 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181113 p = 1 := by simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24354 p hg
    simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24366 (p : Pattern) (guard : d181125 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181120 p = 1 := by simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24361 p hg
    simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181124 p = 1 := by simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24365 p hg
    simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24367 (p : Pattern) (guard : d181126 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181125 p = 1 := by simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24366 p hg
    simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24368 (p : Pattern) (guard : d181127 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181126 p = 1 := by simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24367 p hg
    simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24369 (p : Pattern) (guard : d181128 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181123 p = 1 := by simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24364 p hg
    simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181127 p = 1 := by simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24368 p hg
    simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24370 (p : Pattern) (guard : d181129 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181118 p = 1 := by simpa only [d181129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24359 p hg
    simpa only [d181129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181128 p = 1 := by simpa only [d181129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24369 p hg
    simpa only [d181129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24371 (p : Pattern) (guard : d181130 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181129 p = 1 := by simpa only [d181130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24370 p hg
    simpa only [d181130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24372 (p : Pattern) (guard : d181131 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181130 p = 1 := by simpa only [d181131, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24371 p hg
    simpa only [d181131, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181131, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181131, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24373 (p : Pattern) (guard : d181132 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181132, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181132, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181131 p = 1 := by simpa only [d181132, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24372 p hg
    simpa only [d181132, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24374 (p : Pattern) (guard : d181133 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181127 p = 1 := by simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24368 p hg
    simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24375 (p : Pattern) (guard : d181134 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181128 p = 1 := by simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24369 p hg
    simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181133 p = 1 := by simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24374 p hg
    simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24376 (p : Pattern) (guard : d181135 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181134 p = 1 := by simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24375 p hg
    simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24377 (p : Pattern) (guard : d181136 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181135 p = 1 := by simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24376 p hg
    simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24378 (p : Pattern) (guard : d181137 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181136 p = 1 := by simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24377 p hg
    simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24379 (p : Pattern) (guard : d181138 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181132 p = 1 := by simpa only [d181138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24373 p hg
    simpa only [d181138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181137 p = 1 := by simpa only [d181138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24378 p hg
    simpa only [d181138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24380 (p : Pattern) (guard : d181139 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181138 p = 1 := by simpa only [d181139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24379 p hg
    simpa only [d181139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24381 (p : Pattern) (guard : d181140 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181139 p = 1 := by simpa only [d181140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24380 p hg
    simpa only [d181140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24382 (p : Pattern) (guard : d181141 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181140 p = 1 := by simpa only [d181141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24381 p hg
    simpa only [d181141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24383 (p : Pattern) (guard : d181142 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181133 p = 1 := by simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24374 p hg
    simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24384 (p : Pattern) (guard : d181143 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181142 p = 1 := by simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24383 p hg
    simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24385 (p : Pattern) (guard : d181144 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181143 p = 1 := by simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24384 p hg
    simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24386 (p : Pattern) (guard : d181145 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181144 p = 1 := by simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24385 p hg
    simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24387 (p : Pattern) (guard : d181146 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181137 p = 1 := by simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24378 p hg
    simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181145 p = 1 := by simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24386 p hg
    simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24388 (p : Pattern) (guard : d181147 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181146 p = 1 := by simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24387 p hg
    simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24389 (p : Pattern) (guard : d181148 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181147 p = 1 := by simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24388 p hg
    simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24390 (p : Pattern) (guard : d181149 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181148 p = 1 := by simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24389 p hg
    simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24391 (p : Pattern) (guard : d181150 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181141 p = 1 := by simpa only [d181150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d181150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181149 p = 1 := by simpa only [d181150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24390 p hg
    simpa only [d181150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24392 (p : Pattern) (guard : d181151 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181150 p = 1 := by simpa only [d181151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24391 p hg
    simpa only [d181151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24393 (p : Pattern) (guard : d181152 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181137 p = 1 := by simpa only [d181152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24378 p hg
    simpa only [d181152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24394 (p : Pattern) (guard : d181153 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181152 p = 1 := by simpa only [d181153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24393 p hg
    simpa only [d181153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24395 (p : Pattern) (guard : d181154 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181153 p = 1 := by simpa only [d181154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24394 p hg
    simpa only [d181154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24396 (p : Pattern) (guard : d181155 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181154 p = 1 := by simpa only [d181155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24395 p hg
    simpa only [d181155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24397 (p : Pattern) (guard : d181156 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181155 p = 1 := by simpa only [d181156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24396 p hg
    simpa only [d181156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24398 (p : Pattern) (guard : d181157 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d181156 p = 1 := by simpa only [d181157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24397 p hg
    simpa only [d181157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24399 (p : Pattern) (guard : d181158 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181151 p = 1 := by simpa only [d181158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24392 p hg
    simpa only [d181158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181157 p = 1 := by simpa only [d181158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24398 p hg
    simpa only [d181158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24400 (p : Pattern) (guard : d181159 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181158 p = 1 := by simpa only [d181159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24399 p hg
    simpa only [d181159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24401 (p : Pattern) (guard : d181160 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181159 p = 1 := by simpa only [d181160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24400 p hg
    simpa only [d181160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24402 (p : Pattern) (guard : d181161 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181161, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181161, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181160 p = 1 := by simpa only [d181161, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24401 p hg
    simpa only [d181161, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24403 (p : Pattern) (guard : d181162 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181161 p = 1 := by simpa only [d181162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24402 p hg
    simpa only [d181162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24404 (p : Pattern) (guard : d181163 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181145 p = 1 := by simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24386 p hg
    simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24405 (p : Pattern) (guard : d181164 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181163 p = 1 := by simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24404 p hg
    simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24406 (p : Pattern) (guard : d181165 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181164 p = 1 := by simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24405 p hg
    simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24407 (p : Pattern) (guard : d181166 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181165 p = 1 := by simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24406 p hg
    simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24408 (p : Pattern) (guard : d181167 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181166 p = 1 := by simpa only [d181167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24407 p hg
    simpa only [d181167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24409 (p : Pattern) (guard : d181168 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181167 p = 1 := by simpa only [d181168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24408 p hg
    simpa only [d181168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24410 (p : Pattern) (guard : d181169 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181168 p = 1 := by simpa only [d181169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24409 p hg
    simpa only [d181169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24411 (p : Pattern) (guard : d181170 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181169 p = 1 := by simpa only [d181170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24410 p hg
    simpa only [d181170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24412 (p : Pattern) (guard : d181171 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181170 p = 1 := by simpa only [d181171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24411 p hg
    simpa only [d181171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24413 (p : Pattern) (guard : d181172 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181172, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181172, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181171 p = 1 := by simpa only [d181172, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24412 p hg
    simpa only [d181172, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24414 (p : Pattern) (guard : d181173 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181172 p = 1 := by simpa only [d181173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24413 p hg
    simpa only [d181173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24415 (p : Pattern) (guard : d181174 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181162 p = 1 := by simpa only [d181174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24403 p hg
    simpa only [d181174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181173 p = 1 := by simpa only [d181174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24414 p hg
    simpa only [d181174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24416 (p : Pattern) (guard : d181175 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181174 p = 1 := by simpa only [d181175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24415 p hg
    simpa only [d181175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24417 (p : Pattern) (guard : d181176 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181175 p = 1 := by simpa only [d181176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24416 p hg
    simpa only [d181176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24418 (p : Pattern) (guard : d181177 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181176 p = 1 := by simpa only [d181177, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24417 p hg
    simpa only [d181177, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181177, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d181177, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24419 (p : Pattern) (guard : d181178 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181178, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d181178, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181177 p = 1 := by simpa only [d181178, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24418 p hg
    simpa only [d181178, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24420 (p : Pattern) (guard : d181179 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181178 p = 1 := by simpa only [d181179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24419 p hg
    simpa only [d181179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24421 (p : Pattern) (guard : d181180 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181179 p = 1 := by simpa only [d181180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24420 p hg
    simpa only [d181180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24422 (p : Pattern) (guard : d181181 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181180 p = 1 := by simpa only [d181181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24421 p hg
    simpa only [d181181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24423 (p : Pattern) (guard : d181182 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181181 p = 1 := by simpa only [d181182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24422 p hg
    simpa only [d181182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24424 (p : Pattern) (guard : d181183 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181182 p = 1 := by simpa only [d181183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24423 p hg
    simpa only [d181183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24425 (p : Pattern) (guard : d181184 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181183 p = 1 := by simpa only [d181184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24424 p hg
    simpa only [d181184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24426 (p : Pattern) (guard : d181185 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181184 p = 1 := by simpa only [d181185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24425 p hg
    simpa only [d181185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24427 (p : Pattern) (guard : d181186 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d181096 p = 1 := by simpa only [d181186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24329 p hg
    simpa only [d181186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181185 p = 1 := by simpa only [d181186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24426 p hg
    simpa only [d181186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24428 (p : Pattern) (guard : d1376 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24429 (p : Pattern) (guard : d18991 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1376 p = 1 := by simpa only [d18991, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24428 p hg
    simpa only [d18991, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18991, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18991, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24430 (p : Pattern) (guard : d181187 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18991 p = 1 := by simpa only [d181187, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24429 p hg
    simpa only [d181187, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181187, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181187, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24431 (p : Pattern) (guard : d181188 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181187 p = 1 := by simpa only [d181188, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24430 p hg
    simpa only [d181188, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181188, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181188, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24432 (p : Pattern) (guard : d16649 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24433 (p : Pattern) (guard : d18994 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d16649 p = 1 := by simpa only [d18994, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24432 p hg
    simpa only [d18994, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18994, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18994, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24434 (p : Pattern) (guard : d181189 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18994 p = 1 := by simpa only [d181189, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24433 p hg
    simpa only [d181189, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181189, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181189, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24435 (p : Pattern) (guard : d181190 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181189 p = 1 := by simpa only [d181190, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24434 p hg
    simpa only [d181190, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181190, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181190, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24436 (p : Pattern) (guard : d181191 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181188 p = 1 := by simpa only [d181191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24431 p hg
    simpa only [d181191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181190 p = 1 := by simpa only [d181191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24435 p hg
    simpa only [d181191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24437 (p : Pattern) (guard : d14987 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24438 (p : Pattern) (guard : d18998 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d14987 p = 1 := by simpa only [d18998, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24437 p hg
    simpa only [d18998, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18998, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18998, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24439 (p : Pattern) (guard : d181192 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18998 p = 1 := by simpa only [d181192, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24438 p hg
    simpa only [d181192, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181192, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181192, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24440 (p : Pattern) (guard : d181193 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181192 p = 1 := by simpa only [d181193, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24439 p hg
    simpa only [d181193, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181193, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181193, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24441 (p : Pattern) (guard : d14994 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24442 (p : Pattern) (guard : d19001 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d14994 p = 1 := by simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24441 p hg
    simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24443 (p : Pattern) (guard : d181194 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19001 p = 1 := by simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24442 p hg
    simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24444 (p : Pattern) (guard : d181195 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181194 p = 1 := by simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24443 p hg
    simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24445 (p : Pattern) (guard : d181196 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181193 p = 1 := by simpa only [d181196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24440 p hg
    simpa only [d181196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181195 p = 1 := by simpa only [d181196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24444 p hg
    simpa only [d181196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24446 (p : Pattern) (guard : d181197 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181191 p = 1 := by simpa only [d181197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24436 p hg
    simpa only [d181197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181196 p = 1 := by simpa only [d181197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24445 p hg
    simpa only [d181197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24447 (p : Pattern) (guard : d1380 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24448 (p : Pattern) (guard : d19006 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1380 p = 1 := by simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24447 p hg
    simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24449 (p : Pattern) (guard : d181198 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19006 p = 1 := by simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24448 p hg
    simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24450 (p : Pattern) (guard : d181199 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181198 p = 1 := by simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24449 p hg
    simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24451 (p : Pattern) (guard : d16656 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24452 (p : Pattern) (guard : d19009 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d16656 p = 1 := by simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24451 p hg
    simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24453 (p : Pattern) (guard : d181200 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19009 p = 1 := by simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24452 p hg
    simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24454 (p : Pattern) (guard : d181201 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181200 p = 1 := by simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24453 p hg
    simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24455 (p : Pattern) (guard : d181202 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181199 p = 1 := by simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24450 p hg
    simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181201 p = 1 := by simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24454 p hg
    simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24456 (p : Pattern) (guard : d15004 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24457 (p : Pattern) (guard : d19013 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15004 p = 1 := by simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24456 p hg
    simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24458 (p : Pattern) (guard : d181203 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19013 p = 1 := by simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24457 p hg
    simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24459 (p : Pattern) (guard : d181204 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181203 p = 1 := by simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24458 p hg
    simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24460 (p : Pattern) (guard : d181205 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181195 p = 1 := by simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24444 p hg
    simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181204 p = 1 := by simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24459 p hg
    simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24461 (p : Pattern) (guard : d181206 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181202 p = 1 := by simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24455 p hg
    simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181205 p = 1 := by simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24460 p hg
    simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24462 (p : Pattern) (guard : d181207 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181197 p = 1 := by simpa only [d181207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24446 p hg
    simpa only [d181207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181206 p = 1 := by simpa only [d181207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24461 p hg
    simpa only [d181207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24463 (p : Pattern) (guard : d181208 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181208, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181208, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181207 p = 1 := by simpa only [d181208, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24462 p hg
    simpa only [d181208, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24464 (p : Pattern) (guard : d181209 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181209, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181209, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181208 p = 1 := by simpa only [d181209, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24463 p hg
    simpa only [d181209, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24465 (p : Pattern) (guard : d13160 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24466 (p : Pattern) (guard : d19021 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13160 p = 1 := by simpa only [d19021, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24465 p hg
    simpa only [d19021, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19021, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19021, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24467 (p : Pattern) (guard : d181210 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19021 p = 1 := by simpa only [d181210, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24466 p hg
    simpa only [d181210, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181210, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181210, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24468 (p : Pattern) (guard : d181211 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181210 p = 1 := by simpa only [d181211, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24467 p hg
    simpa only [d181211, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181211, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181211, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24469 (p : Pattern) (guard : d181212 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181211 p = 1 := by simpa only [d181212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24468 p hg
    simpa only [d181212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181204 p = 1 := by simpa only [d181212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24459 p hg
    simpa only [d181212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24470 (p : Pattern) (guard : d181213 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181204 p = 1 := by simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24459 p hg
    simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24471 (p : Pattern) (guard : d181214 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181212 p = 1 := by simpa only [d181214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24469 p hg
    simpa only [d181214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181213 p = 1 := by simpa only [d181214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24470 p hg
    simpa only [d181214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24472 (p : Pattern) (guard : d181215 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181206 p = 1 := by simpa only [d181215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24461 p hg
    simpa only [d181215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181214 p = 1 := by simpa only [d181215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24471 p hg
    simpa only [d181215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24473 (p : Pattern) (guard : d181216 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181216, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181216, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181215 p = 1 := by simpa only [d181216, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24472 p hg
    simpa only [d181216, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24474 (p : Pattern) (guard : d181217 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181217, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181217, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181216 p = 1 := by simpa only [d181217, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24473 p hg
    simpa only [d181217, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24475 (p : Pattern) (guard : d181218 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181209 p = 1 := by simpa only [d181218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24464 p hg
    simpa only [d181218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181217 p = 1 := by simpa only [d181218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24474 p hg
    simpa only [d181218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24476 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24477 (p : Pattern) (guard : d19031 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24476 p hg
    simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24478 (p : Pattern) (guard : d181219 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19031 p = 1 := by simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24477 p hg
    simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24479 (p : Pattern) (guard : d181220 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181219 p = 1 := by simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24478 p hg
    simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24480 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24481 (p : Pattern) (guard : d19034 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24480 p hg
    simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24482 (p : Pattern) (guard : d181221 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19034 p = 1 := by simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24481 p hg
    simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24483 (p : Pattern) (guard : d181222 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181221 p = 1 := by simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24482 p hg
    simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24484 (p : Pattern) (guard : d181223 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181220 p = 1 := by simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24479 p hg
    simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181222 p = 1 := by simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24483 p hg
    simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24485 (p : Pattern) (guard : d181224 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181223 p = 1 := by simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24484 p hg
    simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181213 p = 1 := by simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24470 p hg
    simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24486 (p : Pattern) (guard : d181225 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181206 p = 1 := by simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24461 p hg
    simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181224 p = 1 := by simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24485 p hg
    simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24487 (p : Pattern) (guard : d181226 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181225 p = 1 := by simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24486 p hg
    simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24488 (p : Pattern) (guard : d181227 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181226 p = 1 := by simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24487 p hg
    simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24489 (p : Pattern) (guard : d6350 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24490 (p : Pattern) (guard : d19042 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6350 p = 1 := by simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24489 p hg
    simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24491 (p : Pattern) (guard : d181228 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19042 p = 1 := by simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24490 p hg
    simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24492 (p : Pattern) (guard : d181229 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181228 p = 1 := by simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24491 p hg
    simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24493 (p : Pattern) (guard : d181230 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181229 p = 1 := by simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24492 p hg
    simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24494 (p : Pattern) (guard : d15019 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24495 (p : Pattern) (guard : d19046 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15019 p = 1 := by simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24494 p hg
    simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24496 (p : Pattern) (guard : d181231 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19046 p = 1 := by simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24495 p hg
    simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24497 (p : Pattern) (guard : d181232 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181231 p = 1 := by simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24496 p hg
    simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24498 (p : Pattern) (guard : d181233 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181232 p = 1 := by simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24497 p hg
    simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24499 (p : Pattern) (guard : d181234 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181230 p = 1 := by simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24493 p hg
    simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181233 p = 1 := by simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24498 p hg
    simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
