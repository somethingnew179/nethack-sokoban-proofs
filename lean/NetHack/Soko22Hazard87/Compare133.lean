import NetHack.Soko22Hazard87.Compare132
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33250 (p : Pattern) (guard : d295133 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295111 p = 1 := by simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33249 p hg
    simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33251 (p : Pattern) (guard : d295134 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295133 p = 1 := by simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33250 p hg
    simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33252 (p : Pattern) (guard : d295135 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295134 p = 1 := by simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33251 p hg
    simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33253 (p : Pattern) (guard : d295136 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295132 p = 1 := by simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295135 p = 1 := by simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33252 p hg
    simpa only [d295136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33254 (p : Pattern) (guard : d295157 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295136 p = 1 := by simpa only [d295157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33253 p hg
    simpa only [d295157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33255 (p : Pattern) (guard : d295158 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295157 p = 1 := by simpa only [d295158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33254 p hg
    simpa only [d295158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33256 (p : Pattern) (guard : d295159 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295159, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295159, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295158 p = 1 := by simpa only [d295159, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33255 p hg
    simpa only [d295159, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33257 (p : Pattern) (guard : d295160 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295159 p = 1 := by simpa only [d295160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33256 p hg
    simpa only [d295160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33258 (p : Pattern) (guard : d295055 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295050 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33240 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33259 (p : Pattern) (guard : d295056 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295055 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33258 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33260 (p : Pattern) (guard : d295057 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295056 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33259 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33261 (p : Pattern) (guard : d295068 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295057 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33262 (p : Pattern) (guard : d295147 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295068 p = 1 := by simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33261 p hg
    simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33263 (p : Pattern) (guard : d295148 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295147 p = 1 := by simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33262 p hg
    simpa only [d295148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33264 (p : Pattern) (guard : d295149 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295148 p = 1 := by simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33263 p hg
    simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33265 (p : Pattern) (guard : d295150 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295149 p = 1 := by simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33264 p hg
    simpa only [d295150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33266 (p : Pattern) (guard : d295151 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295150 p = 1 := by simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33265 p hg
    simpa only [d295151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33267 (p : Pattern) (guard : d295161 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295161, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295161, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295151 p = 1 := by simpa only [d295161, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33266 p hg
    simpa only [d295161, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33268 (p : Pattern) (guard : d295162 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295161 p = 1 := by simpa only [d295162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33267 p hg
    simpa only [d295162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33269 (p : Pattern) (guard : d295163 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295160 p = 1 := by simpa only [d295163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33257 p hg
    simpa only [d295163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295162 p = 1 := by simpa only [d295163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33268 p hg
    simpa only [d295163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33270 (p : Pattern) (guard : d295164 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295163 p = 1 := by simpa only [d295164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33269 p hg
    simpa only [d295164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33271 (p : Pattern) (guard : d295165 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295164 p = 1 := by simpa only [d295165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33270 p hg
    simpa only [d295165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33272 (p : Pattern) (guard : d295166 p = 1) : d50002 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295156 p = 1 := by simpa only [d295166, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33200 p hg
    simpa only [d295166, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295165 p = 1 := by simpa only [d295166, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33271 p hg
    simpa only [d295166, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33273 (p : Pattern) (guard : d293903 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32890 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33274 (p : Pattern) (guard : d293904 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33273 p hg
    simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33275 (p : Pattern) (guard : d293905 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33274 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33276 (p : Pattern) (guard : d294084 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293905 p = 1 := by simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33275 p hg
    simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33277 (p : Pattern) (guard : d293906 p = 1) : d50030 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33001 p hg
    simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33278 (p : Pattern) (guard : d294085 p = 1) : d50031 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294084 p = 1 := by simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33276 p hg
    simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293906 p = 1 := by simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33277 p hg
    simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33279 (p : Pattern) (guard : d293903 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32901 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33280 (p : Pattern) (guard : d293904 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33279 p hg
    simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33281 (p : Pattern) (guard : d293905 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33280 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33282 (p : Pattern) (guard : d293906 p = 1) : d49865 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33281 p hg
    simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33283 (p : Pattern) (guard : d293907 p = 1) : d49866 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293906 p = 1 := by simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33282 p hg
    simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33284 (p : Pattern) (guard : d294086 p = 1) : d50032 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294085 p = 1 := by simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33278 p hg
    simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293907 p = 1 := by simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33285 (p : Pattern) (guard : d294087 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294086 p = 1 := by simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33284 p hg
    simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33286 (p : Pattern) (guard : d295167 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294087 p = 1 := by simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33285 p hg
    simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33287 (p : Pattern) (guard : d295168 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294955 p = 1 := by simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32909 p hg
    simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295167 p = 1 := by simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33286 p hg
    simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33288 (p : Pattern) (guard : d295169 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295168 p = 1 := by simpa only [d295169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33287 p hg
    simpa only [d295169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33289 (p : Pattern) (guard : d295170 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295170, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d295170, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295169 p = 1 := by simpa only [d295170, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33288 p hg
    simpa only [d295170, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33290 (p : Pattern) (guard : d295171 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295171, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d295171, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295170 p = 1 := by simpa only [d295171, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33289 p hg
    simpa only [d295171, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33291 (p : Pattern) (guard : d294098 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294087 p = 1 := by simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33285 p hg
    simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33292 (p : Pattern) (guard : d295172 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295167 p = 1 := by simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33286 p hg
    simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294098 p = 1 := by simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33293 (p : Pattern) (guard : d295173 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295168 p = 1 := by simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33287 p hg
    simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295172 p = 1 := by simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33292 p hg
    simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33294 (p : Pattern) (guard : d295174 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295173 p = 1 := by simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33293 p hg
    simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33295 (p : Pattern) (guard : d295175 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295174 p = 1 := by simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33294 p hg
    simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33296 (p : Pattern) (guard : d295176 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295171 p = 1 := by simpa only [d295176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33290 p hg
    simpa only [d295176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295175 p = 1 := by simpa only [d295176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33295 p hg
    simpa only [d295176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33297 (p : Pattern) (guard : d295177 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294098 p = 1 := by simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33298 (p : Pattern) (guard : d295178 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295172 p = 1 := by simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33292 p hg
    simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295177 p = 1 := by simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33297 p hg
    simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33299 (p : Pattern) (guard : d295179 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295178 p = 1 := by simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33298 p hg
    simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33300 (p : Pattern) (guard : d295180 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295179 p = 1 := by simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33299 p hg
    simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33301 (p : Pattern) (guard : d295181 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295175 p = 1 := by simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33295 p hg
    simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295180 p = 1 := by simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33300 p hg
    simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33302 (p : Pattern) (guard : d295182 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295176 p = 1 := by simpa only [d295182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33296 p hg
    simpa only [d295182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295181 p = 1 := by simpa only [d295182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33301 p hg
    simpa only [d295182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33303 (p : Pattern) (guard : d295183 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295182 p = 1 := by simpa only [d295183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33302 p hg
    simpa only [d295183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33304 (p : Pattern) (guard : d295184 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295183 p = 1 := by simpa only [d295184, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33303 p hg
    simpa only [d295184, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295184, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d295184, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33305 (p : Pattern) (guard : d295185 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295185, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295185, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295184 p = 1 := by simpa only [d295185, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33304 p hg
    simpa only [d295185, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33306 (p : Pattern) (guard : d295186 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295180 p = 1 := by simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33300 p hg
    simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33307 (p : Pattern) (guard : d295187 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295181 p = 1 := by simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33301 p hg
    simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295186 p = 1 := by simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33306 p hg
    simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33308 (p : Pattern) (guard : d295188 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295187 p = 1 := by simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33307 p hg
    simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33309 (p : Pattern) (guard : d295189 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295188 p = 1 := by simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33308 p hg
    simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33310 (p : Pattern) (guard : d295190 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295189 p = 1 := by simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33309 p hg
    simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33311 (p : Pattern) (guard : d295191 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295185 p = 1 := by simpa only [d295191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33305 p hg
    simpa only [d295191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295190 p = 1 := by simpa only [d295191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33310 p hg
    simpa only [d295191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33312 (p : Pattern) (guard : d295192 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295191 p = 1 := by simpa only [d295192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33311 p hg
    simpa only [d295192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33313 (p : Pattern) (guard : d295193 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295192 p = 1 := by simpa only [d295193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33312 p hg
    simpa only [d295193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33314 (p : Pattern) (guard : d295194 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295193 p = 1 := by simpa only [d295194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33313 p hg
    simpa only [d295194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33315 (p : Pattern) (guard : d295195 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295186 p = 1 := by simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33306 p hg
    simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33316 (p : Pattern) (guard : d295196 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295195 p = 1 := by simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33315 p hg
    simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33317 (p : Pattern) (guard : d295197 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295196 p = 1 := by simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33316 p hg
    simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33318 (p : Pattern) (guard : d295198 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295197 p = 1 := by simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33317 p hg
    simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33319 (p : Pattern) (guard : d295199 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295190 p = 1 := by simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33310 p hg
    simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295198 p = 1 := by simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33318 p hg
    simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33320 (p : Pattern) (guard : d295200 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295199 p = 1 := by simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33319 p hg
    simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33321 (p : Pattern) (guard : d295201 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295200 p = 1 := by simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33320 p hg
    simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33322 (p : Pattern) (guard : d295202 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295201 p = 1 := by simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33321 p hg
    simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33323 (p : Pattern) (guard : d295203 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295194 p = 1 := by simpa only [d295203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33314 p hg
    simpa only [d295203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295202 p = 1 := by simpa only [d295203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33322 p hg
    simpa only [d295203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33324 (p : Pattern) (guard : d295204 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295203 p = 1 := by simpa only [d295204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33323 p hg
    simpa only [d295204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33325 (p : Pattern) (guard : d295205 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295190 p = 1 := by simpa only [d295205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33310 p hg
    simpa only [d295205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33326 (p : Pattern) (guard : d295206 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295205 p = 1 := by simpa only [d295206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33325 p hg
    simpa only [d295206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33327 (p : Pattern) (guard : d295207 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295206 p = 1 := by simpa only [d295207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d295207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33328 (p : Pattern) (guard : d295208 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295207 p = 1 := by simpa only [d295208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33327 p hg
    simpa only [d295208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33329 (p : Pattern) (guard : d295209 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295208 p = 1 := by simpa only [d295209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33328 p hg
    simpa only [d295209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33330 (p : Pattern) (guard : d295210 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295209 p = 1 := by simpa only [d295210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33329 p hg
    simpa only [d295210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33331 (p : Pattern) (guard : d295211 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295204 p = 1 := by simpa only [d295211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33324 p hg
    simpa only [d295211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295210 p = 1 := by simpa only [d295211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33330 p hg
    simpa only [d295211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33332 (p : Pattern) (guard : d295212 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295211 p = 1 := by simpa only [d295212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33331 p hg
    simpa only [d295212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33333 (p : Pattern) (guard : d295213 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295212 p = 1 := by simpa only [d295213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33332 p hg
    simpa only [d295213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33334 (p : Pattern) (guard : d295214 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295214, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295214, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295213 p = 1 := by simpa only [d295214, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33333 p hg
    simpa only [d295214, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33335 (p : Pattern) (guard : d295215 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295214 p = 1 := by simpa only [d295215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33334 p hg
    simpa only [d295215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33336 (p : Pattern) (guard : d295216 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295198 p = 1 := by simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33318 p hg
    simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33337 (p : Pattern) (guard : d295217 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295216 p = 1 := by simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33336 p hg
    simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33338 (p : Pattern) (guard : d295218 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295217 p = 1 := by simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33337 p hg
    simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33339 (p : Pattern) (guard : d295219 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295218 p = 1 := by simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33338 p hg
    simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33340 (p : Pattern) (guard : d295220 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295219 p = 1 := by simpa only [d295220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33339 p hg
    simpa only [d295220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33341 (p : Pattern) (guard : d295221 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295220 p = 1 := by simpa only [d295221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33340 p hg
    simpa only [d295221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33342 (p : Pattern) (guard : d295222 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295221 p = 1 := by simpa only [d295222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33341 p hg
    simpa only [d295222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33343 (p : Pattern) (guard : d295223 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295222 p = 1 := by simpa only [d295223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33342 p hg
    simpa only [d295223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33344 (p : Pattern) (guard : d295224 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295223 p = 1 := by simpa only [d295224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33343 p hg
    simpa only [d295224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33345 (p : Pattern) (guard : d295225 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295225, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295225, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295224 p = 1 := by simpa only [d295225, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33344 p hg
    simpa only [d295225, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33346 (p : Pattern) (guard : d295226 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295225 p = 1 := by simpa only [d295226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33345 p hg
    simpa only [d295226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33347 (p : Pattern) (guard : d295227 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295215 p = 1 := by simpa only [d295227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33335 p hg
    simpa only [d295227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295226 p = 1 := by simpa only [d295227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33346 p hg
    simpa only [d295227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33348 (p : Pattern) (guard : d295228 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295227 p = 1 := by simpa only [d295228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33347 p hg
    simpa only [d295228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33349 (p : Pattern) (guard : d295229 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295228 p = 1 := by simpa only [d295229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33348 p hg
    simpa only [d295229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d295229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33350 (p : Pattern) (guard : d295230 p = 1) : d50100 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295229 p = 1 := by simpa only [d295230, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33349 p hg
    simpa only [d295230, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295230, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32160 p hg
    simpa only [d295230, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33351 (p : Pattern) (guard : d295231 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d295166 p = 1 := by simpa only [d295231, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33272 p hg
    simpa only [d295231, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295230 p = 1 := by simpa only [d295231, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33350 p hg
    simpa only [d295231, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33352 (p : Pattern) (guard : d295232 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295231 p = 1 := by simpa only [d295232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33351 p hg
    simpa only [d295232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33353 (p : Pattern) (guard : d295233 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295232 p = 1 := by simpa only [d295233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33352 p hg
    simpa only [d295233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33354 (p : Pattern) (guard : d295234 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295233 p = 1 := by simpa only [d295234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33353 p hg
    simpa only [d295234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33355 (p : Pattern) (guard : d295235 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295234 p = 1 := by simpa only [d295235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33354 p hg
    simpa only [d295235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33356 (p : Pattern) (guard : d295236 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295235 p = 1 := by simpa only [d295236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33355 p hg
    simpa only [d295236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33357 (p : Pattern) (guard : d295237 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295236 p = 1 := by simpa only [d295237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33356 p hg
    simpa only [d295237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33358 (p : Pattern) (guard : d295238 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295237 p = 1 := by simpa only [d295238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33357 p hg
    simpa only [d295238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33359 (p : Pattern) (guard : d295239 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295238 p = 1 := by simpa only [d295239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33358 p hg
    simpa only [d295239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33360 (p : Pattern) (guard : d295240 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d295240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295239 p = 1 := by simpa only [d295240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33359 p hg
    simpa only [d295240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33361 (p : Pattern) (guard : d295241 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d295030 p = 1 := by simpa only [d295241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32998 p hg
    simpa only [d295241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295240 p = 1 := by simpa only [d295241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33360 p hg
    simpa only [d295241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33362 (p : Pattern) (guard : d2014 p = 1) : d47617 p ≤ (1 : Int) + d47617 p := by
  omega
theorem compare33363 (p : Pattern) (guard : d32701 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33362 p hg
    simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31976 p hg
    simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33364 (p : Pattern) (guard : d32702 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33363 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33365 (p : Pattern) (guard : d32703 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33364 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33366 (p : Pattern) (guard : d294185 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33365 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33367 (p : Pattern) (guard : d294186 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33366 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33368 (p : Pattern) (guard : d294187 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33367 p hg
    simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33369 (p : Pattern) (guard : d294188 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33368 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33370 (p : Pattern) (guard : d294189 p = 1) : d49838 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33369 p hg
    simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33371 (p : Pattern) (guard : d294190 p = 1) : d49841 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294189 p = 1 := by simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33370 p hg
    simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33372 (p : Pattern) (guard : d294191 p = 1) : d49864 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294190 p = 1 := by simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33371 p hg
    simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33373 (p : Pattern) (guard : d294192 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294191 p = 1 := by simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33372 p hg
    simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33374 (p : Pattern) (guard : d295242 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294192 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33373 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33375 (p : Pattern) (guard : d295243 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295242 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33374 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33376 (p : Pattern) (guard : d294204 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294192 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33373 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33377 (p : Pattern) (guard : d295244 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295242 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33374 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294204 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33378 (p : Pattern) (guard : d295245 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295243 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33375 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295244 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33377 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33379 (p : Pattern) (guard : d295246 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295245 p = 1 := by simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33378 p hg
    simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33380 (p : Pattern) (guard : d295247 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295246 p = 1 := by simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33381 (p : Pattern) (guard : d295248 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294204 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33382 (p : Pattern) (guard : d295249 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295244 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33377 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295248 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33381 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33383 (p : Pattern) (guard : d295250 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295249 p = 1 := by simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33382 p hg
    simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33384 (p : Pattern) (guard : d295251 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295250 p = 1 := by simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33383 p hg
    simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33385 (p : Pattern) (guard : d295252 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295247 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295251 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33384 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33386 (p : Pattern) (guard : d295253 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295251 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33384 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33387 (p : Pattern) (guard : d295254 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33385 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295253 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33386 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33388 (p : Pattern) (guard : d295255 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295254 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33387 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33389 (p : Pattern) (guard : d295256 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295255 p = 1 := by simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33388 p hg
    simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33390 (p : Pattern) (guard : d295257 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295256 p = 1 := by simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33389 p hg
    simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33391 (p : Pattern) (guard : d295258 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295253 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33386 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33392 (p : Pattern) (guard : d295259 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295258 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33391 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33393 (p : Pattern) (guard : d295260 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295259 p = 1 := by simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33392 p hg
    simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33394 (p : Pattern) (guard : d295261 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295260 p = 1 := by simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33393 p hg
    simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33395 (p : Pattern) (guard : d295262 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295257 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33390 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295261 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33394 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33396 (p : Pattern) (guard : d295263 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295262 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33395 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33397 (p : Pattern) (guard : d295264 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295263 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33396 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33398 (p : Pattern) (guard : d295265 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295264 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33397 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33399 (p : Pattern) (guard : d295266 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295261 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33394 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33400 (p : Pattern) (guard : d295267 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295266 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33399 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33401 (p : Pattern) (guard : d295268 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295267 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33400 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33402 (p : Pattern) (guard : d295269 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295268 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33401 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33403 (p : Pattern) (guard : d295270 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295265 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33398 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295269 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33402 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33404 (p : Pattern) (guard : d295271 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295270 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33403 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33405 (p : Pattern) (guard : d295272 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295271 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33404 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33406 (p : Pattern) (guard : d295273 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295272 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33405 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33407 (p : Pattern) (guard : d295274 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295273 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33406 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33408 (p : Pattern) (guard : d295275 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295274 p = 1 := by simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33407 p hg
    simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33409 (p : Pattern) (guard : d295276 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295275 p = 1 := by simpa only [d295276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33408 p hg
    simpa only [d295276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33410 (p : Pattern) (guard : d295277 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295276 p = 1 := by simpa only [d295277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33409 p hg
    simpa only [d295277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33411 (p : Pattern) (guard : d295247 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295246 p = 1 := by simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33412 (p : Pattern) (guard : d295251 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295250 p = 1 := by simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33383 p hg
    simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33413 (p : Pattern) (guard : d295252 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295247 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33411 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295251 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33412 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33414 (p : Pattern) (guard : d295253 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295251 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33412 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33415 (p : Pattern) (guard : d295254 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33413 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295253 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33414 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33416 (p : Pattern) (guard : d295255 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295254 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33415 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33417 (p : Pattern) (guard : d295256 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295255 p = 1 := by simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33416 p hg
    simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33418 (p : Pattern) (guard : d295257 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295256 p = 1 := by simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33417 p hg
    simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33419 (p : Pattern) (guard : d295258 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295253 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33414 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33420 (p : Pattern) (guard : d295259 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295258 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33419 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33421 (p : Pattern) (guard : d295260 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295259 p = 1 := by simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33420 p hg
    simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33422 (p : Pattern) (guard : d295261 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295260 p = 1 := by simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33421 p hg
    simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33423 (p : Pattern) (guard : d295262 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295257 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33418 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295261 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33422 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33424 (p : Pattern) (guard : d295263 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295262 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33423 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33425 (p : Pattern) (guard : d295264 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295263 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33424 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33426 (p : Pattern) (guard : d295265 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295264 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33425 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33427 (p : Pattern) (guard : d295266 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295261 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33422 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33428 (p : Pattern) (guard : d295267 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295266 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33427 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33429 (p : Pattern) (guard : d295268 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295267 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33428 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33430 (p : Pattern) (guard : d295269 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295268 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33429 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33431 (p : Pattern) (guard : d295270 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295265 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33426 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295269 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33430 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33432 (p : Pattern) (guard : d295271 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295270 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33431 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33433 (p : Pattern) (guard : d295272 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295271 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33432 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33434 (p : Pattern) (guard : d295273 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295272 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33433 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33435 (p : Pattern) (guard : d295274 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295273 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33434 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33436 (p : Pattern) (guard : d295278 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295264 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33397 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33437 (p : Pattern) (guard : d295279 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295268 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33401 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33438 (p : Pattern) (guard : d295280 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295278 p = 1 := by simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33436 p hg
    simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295279 p = 1 := by simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33437 p hg
    simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33439 (p : Pattern) (guard : d295281 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295280 p = 1 := by simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33438 p hg
    simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33440 (p : Pattern) (guard : d295282 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295281 p = 1 := by simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33439 p hg
    simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33441 (p : Pattern) (guard : d295283 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295282 p = 1 := by simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33440 p hg
    simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33442 (p : Pattern) (guard : d295284 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295283 p = 1 := by simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33441 p hg
    simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33443 (p : Pattern) (guard : d295285 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295274 p = 1 := by simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33435 p hg
    simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295284 p = 1 := by simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33442 p hg
    simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33444 (p : Pattern) (guard : d295286 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295275 p = 1 := by simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33408 p hg
    simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295285 p = 1 := by simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33443 p hg
    simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33445 (p : Pattern) (guard : d295287 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295286 p = 1 := by simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33444 p hg
    simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33446 (p : Pattern) (guard : d295288 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295277 p = 1 := by simpa only [d295288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33410 p hg
    simpa only [d295288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295287 p = 1 := by simpa only [d295288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33445 p hg
    simpa only [d295288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33447 (p : Pattern) (guard : d295289 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295263 p = 1 := by simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33396 p hg
    simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33448 (p : Pattern) (guard : d295290 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295289 p = 1 := by simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33447 p hg
    simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33449 (p : Pattern) (guard : d295291 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295267 p = 1 := by simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33400 p hg
    simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33450 (p : Pattern) (guard : d295292 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295291 p = 1 := by simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33449 p hg
    simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33451 (p : Pattern) (guard : d295293 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295290 p = 1 := by simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33448 p hg
    simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295292 p = 1 := by simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33450 p hg
    simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33452 (p : Pattern) (guard : d295294 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295293 p = 1 := by simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33451 p hg
    simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33453 (p : Pattern) (guard : d295295 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295294 p = 1 := by simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33452 p hg
    simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33454 (p : Pattern) (guard : d295296 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295295 p = 1 := by simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33453 p hg
    simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33455 (p : Pattern) (guard : d295297 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295262 p = 1 := by simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33395 p hg
    simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33456 (p : Pattern) (guard : d295298 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295297 p = 1 := by simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33455 p hg
    simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33457 (p : Pattern) (guard : d295299 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295298 p = 1 := by simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33456 p hg
    simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33458 (p : Pattern) (guard : d295300 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295266 p = 1 := by simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33399 p hg
    simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33459 (p : Pattern) (guard : d295301 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295300 p = 1 := by simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33460 (p : Pattern) (guard : d295302 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295301 p = 1 := by simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33459 p hg
    simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33461 (p : Pattern) (guard : d295303 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295299 p = 1 := by simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33457 p hg
    simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295302 p = 1 := by simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33460 p hg
    simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33462 (p : Pattern) (guard : d295304 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295303 p = 1 := by simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33461 p hg
    simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33463 (p : Pattern) (guard : d295305 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295304 p = 1 := by simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33462 p hg
    simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33464 (p : Pattern) (guard : d295306 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295243 p = 1 := by simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33375 p hg
    simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33465 (p : Pattern) (guard : d295307 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295307, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d295307, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295306 p = 1 := by simpa only [d295307, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33464 p hg
    simpa only [d295307, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33466 (p : Pattern) (guard : d295308 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295308, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d295308, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295307 p = 1 := by simpa only [d295308, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33465 p hg
    simpa only [d295308, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33467 (p : Pattern) (guard : d295309 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295308 p = 1 := by simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33466 p hg
    simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295247 p = 1 := by simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33468 (p : Pattern) (guard : d295310 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295309 p = 1 := by simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33467 p hg
    simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295252 p = 1 := by simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33385 p hg
    simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33469 (p : Pattern) (guard : d295311 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295310 p = 1 := by simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33468 p hg
    simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33470 (p : Pattern) (guard : d295312 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295311 p = 1 := by simpa only [d295312, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33469 p hg
    simpa only [d295312, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295312, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295312, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33471 (p : Pattern) (guard : d295313 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295313, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295313, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295312 p = 1 := by simpa only [d295313, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33470 p hg
    simpa only [d295313, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33472 (p : Pattern) (guard : d295314 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295313 p = 1 := by simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33471 p hg
    simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295257 p = 1 := by simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33390 p hg
    simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33473 (p : Pattern) (guard : d295315 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295314 p = 1 := by simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33472 p hg
    simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33474 (p : Pattern) (guard : d295316 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295315 p = 1 := by simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33473 p hg
    simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33475 (p : Pattern) (guard : d295317 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295316 p = 1 := by simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33474 p hg
    simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33476 (p : Pattern) (guard : d295318 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295317 p = 1 := by simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33475 p hg
    simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295265 p = 1 := by simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33398 p hg
    simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33477 (p : Pattern) (guard : d295319 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295318 p = 1 := by simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33476 p hg
    simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33478 (p : Pattern) (guard : d295320 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295242 p = 1 := by simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33374 p hg
    simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33479 (p : Pattern) (guard : d295321 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295320 p = 1 := by simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33478 p hg
    simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33480 (p : Pattern) (guard : d295322 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295322, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d295322, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295321 p = 1 := by simpa only [d295322, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33479 p hg
    simpa only [d295322, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33481 (p : Pattern) (guard : d295323 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295323, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d295323, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295322 p = 1 := by simpa only [d295323, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33480 p hg
    simpa only [d295323, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33482 (p : Pattern) (guard : d295324 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295323 p = 1 := by simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33481 p hg
    simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33483 (p : Pattern) (guard : d295325 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33385 p hg
    simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295324 p = 1 := by simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33482 p hg
    simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33484 (p : Pattern) (guard : d295326 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295325 p = 1 := by simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33483 p hg
    simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33485 (p : Pattern) (guard : d295327 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295326 p = 1 := by simpa only [d295327, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33484 p hg
    simpa only [d295327, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295327, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295327, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33486 (p : Pattern) (guard : d295328 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295328, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295328, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295327 p = 1 := by simpa only [d295328, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33485 p hg
    simpa only [d295328, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33487 (p : Pattern) (guard : d295329 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295328 p = 1 := by simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33486 p hg
    simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33488 (p : Pattern) (guard : d295330 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295329 p = 1 := by simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33487 p hg
    simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33489 (p : Pattern) (guard : d295331 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295330 p = 1 := by simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33488 p hg
    simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33490 (p : Pattern) (guard : d295332 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295331 p = 1 := by simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33489 p hg
    simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33491 (p : Pattern) (guard : d295333 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295332 p = 1 := by simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33490 p hg
    simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33492 (p : Pattern) (guard : d295334 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295333 p = 1 := by simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33491 p hg
    simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33493 (p : Pattern) (guard : d295335 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295319 p = 1 := by simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33477 p hg
    simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295334 p = 1 := by simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33492 p hg
    simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33494 (p : Pattern) (guard : d295336 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d295305 p = 1 := by simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33463 p hg
    simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295335 p = 1 := by simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33493 p hg
    simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33495 (p : Pattern) (guard : d295337 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d295296 p = 1 := by simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33454 p hg
    simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295336 p = 1 := by simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33494 p hg
    simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33496 (p : Pattern) (guard : d295338 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295338, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295338, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295337 p = 1 := by simpa only [d295338, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33495 p hg
    simpa only [d295338, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33497 (p : Pattern) (guard : d295289 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295263 p = 1 := by simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33424 p hg
    simpa only [d295289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33498 (p : Pattern) (guard : d295290 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295289 p = 1 := by simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33497 p hg
    simpa only [d295290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33499 (p : Pattern) (guard : d295291 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295267 p = 1 := by simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33428 p hg
    simpa only [d295291, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
