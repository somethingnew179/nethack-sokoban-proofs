import NetHack.Soko22Hazard87.Compare000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare250 (p : Pattern) (guard : d530 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare249 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare180 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare251 (p : Pattern) (guard : d531 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare250 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare252 (p : Pattern) (guard : d532 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare251 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare253 (p : Pattern) (guard : d533 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare252 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare183 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare254 (p : Pattern) (guard : d534 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare255 (p : Pattern) (guard : d535 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare179 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare254 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare256 (p : Pattern) (guard : d536 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare255 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare118 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare257 (p : Pattern) (guard : d537 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare256 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare258 (p : Pattern) (guard : d538 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare257 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare259 (p : Pattern) (guard : d539 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare258 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare121 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare260 (p : Pattern) (guard : d540 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare253 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare261 (p : Pattern) (guard : d541 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare260 p hg
    simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare262 (p : Pattern) (guard : d542 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare261 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare263 (p : Pattern) (guard : d543 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare262 p hg
    simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare264 (p : Pattern) (guard : d660 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d659 p = 1 := by simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare247 p hg
    simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d543 p = 1 := by simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare263 p hg
    simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare265 (p : Pattern) (guard : d17709 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d660 p = 1 := by simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare264 p hg
    simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare266 (p : Pattern) (guard : d17710 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17709 p = 1 := by simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare265 p hg
    simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare267 (p : Pattern) (guard : d60608 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17710 p = 1 := by simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare266 p hg
    simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17644 p = 1 := by simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare268 (p : Pattern) (guard : d60609 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60608 p = 1 := by simpa only [d60609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare267 p hg
    simpa only [d60609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17645 p = 1 := by simpa only [d60609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare192 p hg
    simpa only [d60609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare269 (p : Pattern) (guard : d60610 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60609 p = 1 := by simpa only [d60610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare268 p hg
    simpa only [d60610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60575 p = 1 := by simpa only [d60610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare193 p hg
    simpa only [d60610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare270 (p : Pattern) (guard : d60611 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60611, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60611, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60610 p = 1 := by simpa only [d60611, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare269 p hg
    simpa only [d60611, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare271 (p : Pattern) (guard : d60612 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60612, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60612, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60611 p = 1 := by simpa only [d60612, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare270 p hg
    simpa only [d60612, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare272 (p : Pattern) (guard : d60613 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60612 p = 1 := by simpa only [d60613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare271 p hg
    simpa only [d60613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60578 p = 1 := by simpa only [d60613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare196 p hg
    simpa only [d60613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare273 (p : Pattern) (guard : d60614 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60613 p = 1 := by simpa only [d60614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d60614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60579 p = 1 := by simpa only [d60614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare197 p hg
    simpa only [d60614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare274 (p : Pattern) (guard : d60615 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60614 p = 1 := by simpa only [d60615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare273 p hg
    simpa only [d60615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare275 (p : Pattern) (guard : d60616 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60615 p = 1 := by simpa only [d60616, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare274 p hg
    simpa only [d60616, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60616, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60616, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare276 (p : Pattern) (guard : d60617 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60617, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60617, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60616 p = 1 := by simpa only [d60617, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare275 p hg
    simpa only [d60617, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare277 (p : Pattern) (guard : d17730 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17599 p = 1 := by simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare278 (p : Pattern) (guard : d60618 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60579 p = 1 := by simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare197 p hg
    simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17730 p = 1 := by simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare279 (p : Pattern) (guard : d60619 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60618 p = 1 := by simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare278 p hg
    simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare280 (p : Pattern) (guard : d60620 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60619 p = 1 := by simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare281 (p : Pattern) (guard : d60621 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60620 p = 1 := by simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare280 p hg
    simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare282 (p : Pattern) (guard : d60622 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60617 p = 1 := by simpa only [d60622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare276 p hg
    simpa only [d60622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60621 p = 1 := by simpa only [d60622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare281 p hg
    simpa only [d60622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare283 (p : Pattern) (guard : d60623 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60622 p = 1 := by simpa only [d60623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d60623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare284 (p : Pattern) (guard : d60624 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60623 p = 1 := by simpa only [d60624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d60624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare285 (p : Pattern) (guard : d60625 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60624 p = 1 := by simpa only [d60625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d60625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare286 (p : Pattern) (guard : d17739 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17730 p = 1 := by simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare287 (p : Pattern) (guard : d17740 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17739 p = 1 := by simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare288 (p : Pattern) (guard : d17741 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17740 p = 1 := by simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare289 (p : Pattern) (guard : d17742 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17741 p = 1 := by simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare288 p hg
    simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare290 (p : Pattern) (guard : d60626 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60621 p = 1 := by simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare281 p hg
    simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17742 p = 1 := by simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare291 (p : Pattern) (guard : d60627 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60626 p = 1 := by simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare290 p hg
    simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare292 (p : Pattern) (guard : d60628 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60627 p = 1 := by simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare291 p hg
    simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare293 (p : Pattern) (guard : d60629 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60628 p = 1 := by simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare292 p hg
    simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare294 (p : Pattern) (guard : d60630 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60625 p = 1 := by simpa only [d60630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare285 p hg
    simpa only [d60630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60629 p = 1 := by simpa only [d60630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d60630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare295 (p : Pattern) (guard : d60631 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60630 p = 1 := by simpa only [d60631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d60631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare296 (p : Pattern) (guard : d60632 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60629 p = 1 := by simpa only [d60632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d60632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare297 (p : Pattern) (guard : d60633 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60632 p = 1 := by simpa only [d60633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare296 p hg
    simpa only [d60633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare298 (p : Pattern) (guard : d60634 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60631 p = 1 := by simpa only [d60634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d60634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60633 p = 1 := by simpa only [d60634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare297 p hg
    simpa only [d60634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare299 (p : Pattern) (guard : d60635 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60634 p = 1 := by simpa only [d60635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare298 p hg
    simpa only [d60635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare300 (p : Pattern) (guard : d60636 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60635 p = 1 := by simpa only [d60636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare299 p hg
    simpa only [d60636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare301 (p : Pattern) (guard : d60637 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60637, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60637, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60636 p = 1 := by simpa only [d60637, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare300 p hg
    simpa only [d60637, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare302 (p : Pattern) (guard : d60638 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60637 p = 1 := by simpa only [d60638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d60638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare303 (p : Pattern) (guard : d17789 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17742 p = 1 := by simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare304 (p : Pattern) (guard : d17790 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17789 p = 1 := by simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare303 p hg
    simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare305 (p : Pattern) (guard : d17791 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17790 p = 1 := by simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare304 p hg
    simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare306 (p : Pattern) (guard : d17792 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17791 p = 1 := by simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare305 p hg
    simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare307 (p : Pattern) (guard : d17793 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17792 p = 1 := by simpa only [d17793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare306 p hg
    simpa only [d17793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare308 (p : Pattern) (guard : d17794 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17793 p = 1 := by simpa only [d17794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare307 p hg
    simpa only [d17794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare309 (p : Pattern) (guard : d17795 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17794 p = 1 := by simpa only [d17795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare308 p hg
    simpa only [d17795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare310 (p : Pattern) (guard : d17796 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17795 p = 1 := by simpa only [d17796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare309 p hg
    simpa only [d17796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare311 (p : Pattern) (guard : d17797 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17796 p = 1 := by simpa only [d17797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare310 p hg
    simpa only [d17797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare312 (p : Pattern) (guard : d17798 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17798, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d17798, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17797 p = 1 := by simpa only [d17798, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d17798, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare313 (p : Pattern) (guard : d17799 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d17799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17798 p = 1 := by simpa only [d17799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare312 p hg
    simpa only [d17799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare314 (p : Pattern) (guard : d60639 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d60638 p = 1 := by simpa only [d60639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d60639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17799 p = 1 := by simpa only [d60639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare313 p hg
    simpa only [d60639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare315 (p : Pattern) (guard : d60640 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d60639 p = 1 := by simpa only [d60640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare314 p hg
    simpa only [d60640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare316 (p : Pattern) (guard : d60641 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d60640 p = 1 := by simpa only [d60641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare315 p hg
    simpa only [d60641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare317 (p : Pattern) (guard : d60642 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d60641 p = 1 := by simpa only [d60642, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare316 p hg
    simpa only [d60642, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60642, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d60642, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare318 (p : Pattern) (guard : d60643 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60643, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d60643, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60642 p = 1 := by simpa only [d60643, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare317 p hg
    simpa only [d60643, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare319 (p : Pattern) (guard : d60644 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60643 p = 1 := by simpa only [d60644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d60644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare320 (p : Pattern) (guard : d60645 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60644 p = 1 := by simpa only [d60645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare319 p hg
    simpa only [d60645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare321 (p : Pattern) (guard : d60646 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60645 p = 1 := by simpa only [d60646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d60646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare322 (p : Pattern) (guard : d60647 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60646 p = 1 := by simpa only [d60647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d60647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare323 (p : Pattern) (guard : d60648 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60647 p = 1 := by simpa only [d60648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare322 p hg
    simpa only [d60648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare324 (p : Pattern) (guard : d60649 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60648 p = 1 := by simpa only [d60649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d60649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare325 (p : Pattern) (guard : d60650 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d60607 p = 1 := by simpa only [d60650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare231 p hg
    simpa only [d60650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60649 p = 1 := by simpa only [d60650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d60650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare326 (p : Pattern) (guard : d820 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare327 (p : Pattern) (guard : d821 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare233 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare328 (p : Pattern) (guard : d822 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare329 (p : Pattern) (guard : d823 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare328 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare330 (p : Pattern) (guard : d824 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare329 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare331 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare332 (p : Pattern) (guard : d826 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare331 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare333 (p : Pattern) (guard : d827 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare239 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare334 (p : Pattern) (guard : d828 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare333 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare335 (p : Pattern) (guard : d829 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare334 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare336 (p : Pattern) (guard : d830 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare335 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare337 (p : Pattern) (guard : d831 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare330 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare336 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare338 (p : Pattern) (guard : d832 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare337 p hg
    simpa only [d832, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d832, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare339 (p : Pattern) (guard : d833 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare338 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare245 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare340 (p : Pattern) (guard : d965 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d965, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d965, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d833 p = 1 := by simpa only [d965, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare339 p hg
    simpa only [d965, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare341 (p : Pattern) (guard : d820 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare248 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare342 (p : Pattern) (guard : d821 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare249 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare343 (p : Pattern) (guard : d822 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare342 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare344 (p : Pattern) (guard : d823 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare343 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare345 (p : Pattern) (guard : d824 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare252 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare346 (p : Pattern) (guard : d825 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare178 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare347 (p : Pattern) (guard : d826 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare248 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare348 (p : Pattern) (guard : d827 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare255 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare349 (p : Pattern) (guard : d828 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare348 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare350 (p : Pattern) (guard : d829 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare349 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare351 (p : Pattern) (guard : d830 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare350 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare258 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare352 (p : Pattern) (guard : d831 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare345 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare351 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare353 (p : Pattern) (guard : d832 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare352 p hg
    simpa only [d832, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d832, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare354 (p : Pattern) (guard : d833 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare353 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare261 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare355 (p : Pattern) (guard : d834 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d834, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d834, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare356 (p : Pattern) (guard : d966 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d965 p = 1 := by simpa only [d966, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare340 p hg
    simpa only [d966, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d834 p = 1 := by simpa only [d966, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare355 p hg
    simpa only [d966, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare357 (p : Pattern) (guard : d17812 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d966 p = 1 := by simpa only [d17812, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare356 p hg
    simpa only [d17812, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17812, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17812, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare358 (p : Pattern) (guard : d17813 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17812 p = 1 := by simpa only [d17813, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d17813, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17813, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17813, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare359 (p : Pattern) (guard : d60651 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17813 p = 1 := by simpa only [d60651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare358 p hg
    simpa only [d60651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17710 p = 1 := by simpa only [d60651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare266 p hg
    simpa only [d60651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare360 (p : Pattern) (guard : d60652 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60651 p = 1 := by simpa only [d60652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare359 p hg
    simpa only [d60652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60608 p = 1 := by simpa only [d60652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare267 p hg
    simpa only [d60652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare361 (p : Pattern) (guard : d750 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare362 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d750 p = 1 := by simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare361 p hg
    simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare363 (p : Pattern) (guard : d750 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare364 (p : Pattern) (guard : d751 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare363 p hg
    simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare365 (p : Pattern) (guard : d972 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare362 p hg
    simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d751 p = 1 := by simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare364 p hg
    simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare366 (p : Pattern) (guard : d17821 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d972 p = 1 := by simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare367 (p : Pattern) (guard : d17822 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17821 p = 1 := by simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare366 p hg
    simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare368 (p : Pattern) (guard : d17834 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17644 p = 1 := by simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17822 p = 1 := by simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare367 p hg
    simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare369 (p : Pattern) (guard : d60653 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60608 p = 1 := by simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare267 p hg
    simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17834 p = 1 := by simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare368 p hg
    simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare370 (p : Pattern) (guard : d60654 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60652 p = 1 := by simpa only [d60654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare360 p hg
    simpa only [d60654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60653 p = 1 := by simpa only [d60654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare369 p hg
    simpa only [d60654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare371 (p : Pattern) (guard : d60655 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60655, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60655, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60654 p = 1 := by simpa only [d60655, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare370 p hg
    simpa only [d60655, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare372 (p : Pattern) (guard : d60656 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60656, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60656, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60655 p = 1 := by simpa only [d60656, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare371 p hg
    simpa only [d60656, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare373 (p : Pattern) (guard : d17828 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17822 p = 1 := by simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare367 p hg
    simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare374 (p : Pattern) (guard : d17835 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17834 p = 1 := by simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare368 p hg
    simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17828 p = 1 := by simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare373 p hg
    simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare375 (p : Pattern) (guard : d60657 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60653 p = 1 := by simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare369 p hg
    simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17835 p = 1 := by simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare374 p hg
    simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare376 (p : Pattern) (guard : d60658 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60657 p = 1 := by simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare375 p hg
    simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare377 (p : Pattern) (guard : d60659 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60658 p = 1 := by simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare376 p hg
    simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare378 (p : Pattern) (guard : d60660 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60656 p = 1 := by simpa only [d60660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare372 p hg
    simpa only [d60660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60659 p = 1 := by simpa only [d60660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare377 p hg
    simpa only [d60660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare379 (p : Pattern) (guard : d17839 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17828 p = 1 := by simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare373 p hg
    simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare380 (p : Pattern) (guard : d17840 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17835 p = 1 := by simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare374 p hg
    simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17839 p = 1 := by simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare379 p hg
    simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare381 (p : Pattern) (guard : d17841 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17840 p = 1 := by simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare380 p hg
    simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare382 (p : Pattern) (guard : d17842 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17841 p = 1 := by simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare383 (p : Pattern) (guard : d60661 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60659 p = 1 := by simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare377 p hg
    simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17842 p = 1 := by simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare382 p hg
    simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare384 (p : Pattern) (guard : d60662 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60660 p = 1 := by simpa only [d60662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare378 p hg
    simpa only [d60662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60661 p = 1 := by simpa only [d60662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d60662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare385 (p : Pattern) (guard : d60663 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60662 p = 1 := by simpa only [d60663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare384 p hg
    simpa only [d60663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare386 (p : Pattern) (guard : d60664 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60663 p = 1 := by simpa only [d60664, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare385 p hg
    simpa only [d60664, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60664, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60664, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare387 (p : Pattern) (guard : d60665 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60665, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60665, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60664 p = 1 := by simpa only [d60665, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare386 p hg
    simpa only [d60665, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare388 (p : Pattern) (guard : d17848 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17842 p = 1 := by simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare382 p hg
    simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare389 (p : Pattern) (guard : d60666 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60661 p = 1 := by simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17848 p = 1 := by simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare388 p hg
    simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare390 (p : Pattern) (guard : d60667 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60666 p = 1 := by simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare389 p hg
    simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare391 (p : Pattern) (guard : d60668 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60667 p = 1 := by simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare390 p hg
    simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare392 (p : Pattern) (guard : d60669 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60668 p = 1 := by simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare391 p hg
    simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare393 (p : Pattern) (guard : d60670 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60665 p = 1 := by simpa only [d60670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d60670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60669 p = 1 := by simpa only [d60670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare392 p hg
    simpa only [d60670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare394 (p : Pattern) (guard : d60671 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60670 p = 1 := by simpa only [d60671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d60671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare395 (p : Pattern) (guard : d60672 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60671 p = 1 := by simpa only [d60672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare394 p hg
    simpa only [d60672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare396 (p : Pattern) (guard : d60673 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60672 p = 1 := by simpa only [d60673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare395 p hg
    simpa only [d60673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare397 (p : Pattern) (guard : d17857 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17848 p = 1 := by simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare388 p hg
    simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare398 (p : Pattern) (guard : d17858 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17857 p = 1 := by simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare397 p hg
    simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare399 (p : Pattern) (guard : d17859 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17858 p = 1 := by simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare400 (p : Pattern) (guard : d17860 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17859 p = 1 := by simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare399 p hg
    simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare401 (p : Pattern) (guard : d60674 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60669 p = 1 := by simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare392 p hg
    simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17860 p = 1 := by simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare400 p hg
    simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare402 (p : Pattern) (guard : d60675 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60674 p = 1 := by simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare401 p hg
    simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare403 (p : Pattern) (guard : d60676 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60675 p = 1 := by simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare402 p hg
    simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare404 (p : Pattern) (guard : d60677 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60676 p = 1 := by simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare403 p hg
    simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare405 (p : Pattern) (guard : d60678 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60673 p = 1 := by simpa only [d60678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare396 p hg
    simpa only [d60678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60677 p = 1 := by simpa only [d60678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare404 p hg
    simpa only [d60678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare406 (p : Pattern) (guard : d60679 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60678 p = 1 := by simpa only [d60679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare405 p hg
    simpa only [d60679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare407 (p : Pattern) (guard : d60680 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60677 p = 1 := by simpa only [d60680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare404 p hg
    simpa only [d60680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare408 (p : Pattern) (guard : d60681 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60680 p = 1 := by simpa only [d60681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare407 p hg
    simpa only [d60681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare409 (p : Pattern) (guard : d60682 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60679 p = 1 := by simpa only [d60682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare406 p hg
    simpa only [d60682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60681 p = 1 := by simpa only [d60682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare408 p hg
    simpa only [d60682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare410 (p : Pattern) (guard : d60683 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60682 p = 1 := by simpa only [d60683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare409 p hg
    simpa only [d60683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare411 (p : Pattern) (guard : d60684 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60683 p = 1 := by simpa only [d60684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare410 p hg
    simpa only [d60684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare412 (p : Pattern) (guard : d60685 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60685, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60685, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60684 p = 1 := by simpa only [d60685, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare411 p hg
    simpa only [d60685, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare413 (p : Pattern) (guard : d60686 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60685 p = 1 := by simpa only [d60686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare412 p hg
    simpa only [d60686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare414 (p : Pattern) (guard : d17918 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17860 p = 1 := by simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare400 p hg
    simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare415 (p : Pattern) (guard : d17919 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17918 p = 1 := by simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare414 p hg
    simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare416 (p : Pattern) (guard : d17920 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17919 p = 1 := by simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare415 p hg
    simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare417 (p : Pattern) (guard : d17921 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17920 p = 1 := by simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare416 p hg
    simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare418 (p : Pattern) (guard : d17922 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17921 p = 1 := by simpa only [d17922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare417 p hg
    simpa only [d17922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare419 (p : Pattern) (guard : d17923 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17922 p = 1 := by simpa only [d17923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d17923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare420 (p : Pattern) (guard : d17924 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17923 p = 1 := by simpa only [d17924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare419 p hg
    simpa only [d17924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare421 (p : Pattern) (guard : d17925 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17924 p = 1 := by simpa only [d17925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare420 p hg
    simpa only [d17925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare422 (p : Pattern) (guard : d17926 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17925 p = 1 := by simpa only [d17926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare421 p hg
    simpa only [d17926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare423 (p : Pattern) (guard : d17927 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17927, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d17927, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17926 p = 1 := by simpa only [d17927, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare422 p hg
    simpa only [d17927, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare424 (p : Pattern) (guard : d17928 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d17928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17927 p = 1 := by simpa only [d17928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare423 p hg
    simpa only [d17928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare425 (p : Pattern) (guard : d60687 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d60686 p = 1 := by simpa only [d60687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare413 p hg
    simpa only [d60687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17928 p = 1 := by simpa only [d60687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare424 p hg
    simpa only [d60687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare426 (p : Pattern) (guard : d60688 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d60687 p = 1 := by simpa only [d60688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare425 p hg
    simpa only [d60688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare427 (p : Pattern) (guard : d60689 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d60688 p = 1 := by simpa only [d60689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare426 p hg
    simpa only [d60689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare428 (p : Pattern) (guard : d60690 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d60689 p = 1 := by simpa only [d60690, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare427 p hg
    simpa only [d60690, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60690, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d60690, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare429 (p : Pattern) (guard : d60691 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60691, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d60691, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60690 p = 1 := by simpa only [d60691, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare428 p hg
    simpa only [d60691, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare430 (p : Pattern) (guard : d60692 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60691 p = 1 := by simpa only [d60692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d60692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare431 (p : Pattern) (guard : d60693 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60692 p = 1 := by simpa only [d60693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare430 p hg
    simpa only [d60693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare432 (p : Pattern) (guard : d60694 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60693 p = 1 := by simpa only [d60694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare431 p hg
    simpa only [d60694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare433 (p : Pattern) (guard : d60695 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60694 p = 1 := by simpa only [d60695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare432 p hg
    simpa only [d60695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare434 (p : Pattern) (guard : d60696 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60695 p = 1 := by simpa only [d60696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare433 p hg
    simpa only [d60696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare435 (p : Pattern) (guard : d60697 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60696 p = 1 := by simpa only [d60697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare434 p hg
    simpa only [d60697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare436 (p : Pattern) (guard : d60698 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60697 p = 1 := by simpa only [d60698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare435 p hg
    simpa only [d60698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare437 (p : Pattern) (guard : d60699 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d60650 p = 1 := by simpa only [d60699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare325 p hg
    simpa only [d60699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60698 p = 1 := by simpa only [d60699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare436 p hg
    simpa only [d60699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare438 (p : Pattern) (guard : d1199 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare439 (p : Pattern) (guard : d1200 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare440 (p : Pattern) (guard : d1201 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare439 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare441 (p : Pattern) (guard : d1202 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare329 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare442 (p : Pattern) (guard : d1203 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare443 (p : Pattern) (guard : d1204 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare442 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare444 (p : Pattern) (guard : d1205 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare443 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare445 (p : Pattern) (guard : d1206 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare335 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare446 (p : Pattern) (guard : d1207 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare441 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare445 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare447 (p : Pattern) (guard : d1208 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare446 p hg
    simpa only [d1208, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1208, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare448 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare449 (p : Pattern) (guard : d1084 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare448 p hg
    simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare101 p hg
    simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare450 (p : Pattern) (guard : d1085 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare451 (p : Pattern) (guard : d1086 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare450 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare452 (p : Pattern) (guard : d1087 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare451 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare453 (p : Pattern) (guard : d1088 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare454 (p : Pattern) (guard : d1089 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare455 (p : Pattern) (guard : d1090 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare329 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare454 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare456 (p : Pattern) (guard : d1091 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare455 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare336 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare457 (p : Pattern) (guard : d1092 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare456 p hg
    simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare458 (p : Pattern) (guard : d1209 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare459 (p : Pattern) (guard : d1376 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1376, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1376, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1209 p = 1 := by simpa only [d1376, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d1376, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare460 (p : Pattern) (guard : d1199 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare461 (p : Pattern) (guard : d1200 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare460 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare462 (p : Pattern) (guard : d1201 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare461 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare463 (p : Pattern) (guard : d1202 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare462 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare464 (p : Pattern) (guard : d1203 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare465 (p : Pattern) (guard : d1204 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare466 (p : Pattern) (guard : d1205 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare465 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare467 (p : Pattern) (guard : d1206 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare466 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare350 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare468 (p : Pattern) (guard : d1207 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare463 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare467 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare469 (p : Pattern) (guard : d1208 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare468 p hg
    simpa only [d1208, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1208, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare470 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare471 (p : Pattern) (guard : d1084 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare470 p hg
    simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare472 (p : Pattern) (guard : d1085 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare473 (p : Pattern) (guard : d1086 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare472 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare474 (p : Pattern) (guard : d1087 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare475 (p : Pattern) (guard : d1088 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare250 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare476 (p : Pattern) (guard : d1089 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare477 (p : Pattern) (guard : d1090 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare478 (p : Pattern) (guard : d1091 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare477 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare351 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare479 (p : Pattern) (guard : d1092 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare478 p hg
    simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare480 (p : Pattern) (guard : d1209 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare469 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare479 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare481 (p : Pattern) (guard : d1210 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d1210, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1210, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare482 (p : Pattern) (guard : d1377 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1376 p = 1 := by simpa only [d1377, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare459 p hg
    simpa only [d1377, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1210 p = 1 := by simpa only [d1377, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare481 p hg
    simpa only [d1377, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare483 (p : Pattern) (guard : d17942 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1377 p = 1 := by simpa only [d17942, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare482 p hg
    simpa only [d17942, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17942, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17942, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare484 (p : Pattern) (guard : d17943 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17942 p = 1 := by simpa only [d17943, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare483 p hg
    simpa only [d17943, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17943, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17943, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare485 (p : Pattern) (guard : d1093 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare451 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare486 (p : Pattern) (guard : d1094 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare167 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare485 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare487 (p : Pattern) (guard : d1095 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare486 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare488 (p : Pattern) (guard : d1096 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare454 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare487 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare489 (p : Pattern) (guard : d1097 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare488 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare243 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare490 (p : Pattern) (guard : d1098 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare489 p hg
    simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare491 (p : Pattern) (guard : d1099 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare492 (p : Pattern) (guard : d1380 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1099 p = 1 := by simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare491 p hg
    simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare493 (p : Pattern) (guard : d1093 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare494 (p : Pattern) (guard : d1094 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare181 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare493 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare495 (p : Pattern) (guard : d1095 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare494 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare496 (p : Pattern) (guard : d1096 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare495 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare497 (p : Pattern) (guard : d1097 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare496 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare498 (p : Pattern) (guard : d1098 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare497 p hg
    simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare499 (p : Pattern) (guard : d1099 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare479 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
