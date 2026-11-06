import NetHack.Soko22Hazard87.Compare016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4250 (p : Pattern) (guard : d62708 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62707 p = 1 := by simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4249 p hg
    simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4251 (p : Pattern) (guard : d62709 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62708 p = 1 := by simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4250 p hg
    simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4252 (p : Pattern) (guard : d2539 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2538 p = 1 := by simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4253 (p : Pattern) (guard : d62710 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2539 p = 1 := by simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4252 p hg
    simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4254 (p : Pattern) (guard : d62711 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62710 p = 1 := by simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4253 p hg
    simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4255 (p : Pattern) (guard : d62712 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62711 p = 1 := by simpa only [d62712, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4254 p hg
    simpa only [d62712, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62712, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d62712, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4256 (p : Pattern) (guard : d62713 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62712 p = 1 := by simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4255 p hg
    simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4257 (p : Pattern) (guard : d62714 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62713 p = 1 := by simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4258 (p : Pattern) (guard : d62715 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62714 p = 1 := by simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4259 (p : Pattern) (guard : d62716 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62715 p = 1 := by simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4258 p hg
    simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4260 (p : Pattern) (guard : d62717 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62716 p = 1 := by simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4261 (p : Pattern) (guard : d62718 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d62709 p = 1 := by simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4251 p hg
    simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62717 p = 1 := by simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4260 p hg
    simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4262 (p : Pattern) (guard : d2552 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2551 p = 1 := by simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4102 p hg
    simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4263 (p : Pattern) (guard : d62719 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2552 p = 1 := by simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4262 p hg
    simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4264 (p : Pattern) (guard : d62720 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62719 p = 1 := by simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4263 p hg
    simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4265 (p : Pattern) (guard : d62721 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62720 p = 1 := by simpa only [d62721, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4264 p hg
    simpa only [d62721, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62721, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d62721, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4266 (p : Pattern) (guard : d62722 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62721 p = 1 := by simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4267 (p : Pattern) (guard : d62723 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62722 p = 1 := by simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4266 p hg
    simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4268 (p : Pattern) (guard : d62724 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62723 p = 1 := by simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4267 p hg
    simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4269 (p : Pattern) (guard : d62725 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62724 p = 1 := by simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4270 (p : Pattern) (guard : d62726 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62725 p = 1 := by simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4269 p hg
    simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4271 (p : Pattern) (guard : d62727 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62726 p = 1 := by simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4270 p hg
    simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4272 (p : Pattern) (guard : d62728 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d62718 p = 1 := by simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62727 p = 1 := by simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4271 p hg
    simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4273 (p : Pattern) (guard : d2566 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2565 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4274 (p : Pattern) (guard : d62729 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2566 p = 1 := by simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4275 (p : Pattern) (guard : d62730 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62729 p = 1 := by simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4274 p hg
    simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4276 (p : Pattern) (guard : d62731 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62730 p = 1 := by simpa only [d62731, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4275 p hg
    simpa only [d62731, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62731, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d62731, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4277 (p : Pattern) (guard : d62732 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62731 p = 1 := by simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4276 p hg
    simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4278 (p : Pattern) (guard : d62733 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62732 p = 1 := by simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4277 p hg
    simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4279 (p : Pattern) (guard : d62734 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62733 p = 1 := by simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4280 (p : Pattern) (guard : d62735 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62734 p = 1 := by simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4279 p hg
    simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4281 (p : Pattern) (guard : d62736 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62735 p = 1 := by simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4280 p hg
    simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4282 (p : Pattern) (guard : d62737 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62736 p = 1 := by simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4281 p hg
    simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4283 (p : Pattern) (guard : d62738 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62737 p = 1 := by simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4282 p hg
    simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4284 (p : Pattern) (guard : d62739 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d62728 p = 1 := by simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4272 p hg
    simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62738 p = 1 := by simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4283 p hg
    simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4285 (p : Pattern) (guard : d2581 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2580 p = 1 := by simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4139 p hg
    simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4286 (p : Pattern) (guard : d62740 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2581 p = 1 := by simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4285 p hg
    simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4287 (p : Pattern) (guard : d62741 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62740 p = 1 := by simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4286 p hg
    simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4288 (p : Pattern) (guard : d62742 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62741 p = 1 := by simpa only [d62742, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4287 p hg
    simpa only [d62742, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62742, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d62742, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4289 (p : Pattern) (guard : d62743 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62742 p = 1 := by simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4288 p hg
    simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4290 (p : Pattern) (guard : d62744 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62743 p = 1 := by simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4289 p hg
    simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4291 (p : Pattern) (guard : d62745 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62744 p = 1 := by simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4290 p hg
    simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4292 (p : Pattern) (guard : d62746 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62745 p = 1 := by simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4293 (p : Pattern) (guard : d62747 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62746 p = 1 := by simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4292 p hg
    simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4294 (p : Pattern) (guard : d62748 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62747 p = 1 := by simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4293 p hg
    simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4295 (p : Pattern) (guard : d62749 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62748 p = 1 := by simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4294 p hg
    simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4296 (p : Pattern) (guard : d62750 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62749 p = 1 := by simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4295 p hg
    simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4297 (p : Pattern) (guard : d62751 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d62739 p = 1 := by simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4284 p hg
    simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62750 p = 1 := by simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4296 p hg
    simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4298 (p : Pattern) (guard : d2597 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2596 p = 1 := by simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4159 p hg
    simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4299 (p : Pattern) (guard : d62752 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2597 p = 1 := by simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4298 p hg
    simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4300 (p : Pattern) (guard : d62753 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62752 p = 1 := by simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4299 p hg
    simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4301 (p : Pattern) (guard : d62754 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62753 p = 1 := by simpa only [d62754, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4300 p hg
    simpa only [d62754, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62754, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d62754, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4302 (p : Pattern) (guard : d62755 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62754 p = 1 := by simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4301 p hg
    simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4303 (p : Pattern) (guard : d62756 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62755 p = 1 := by simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4302 p hg
    simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4304 (p : Pattern) (guard : d62757 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62756 p = 1 := by simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4303 p hg
    simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4305 (p : Pattern) (guard : d62758 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62757 p = 1 := by simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4304 p hg
    simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4306 (p : Pattern) (guard : d62759 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62758 p = 1 := by simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4305 p hg
    simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4307 (p : Pattern) (guard : d62760 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62759 p = 1 := by simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4308 (p : Pattern) (guard : d62761 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62760 p = 1 := by simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4309 (p : Pattern) (guard : d62762 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62761 p = 1 := by simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4310 (p : Pattern) (guard : d62763 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62762 p = 1 := by simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4309 p hg
    simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4311 (p : Pattern) (guard : d62764 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d62751 p = 1 := by simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4297 p hg
    simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62763 p = 1 := by simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4312 (p : Pattern) (guard : d2614 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2613 p = 1 := by simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4180 p hg
    simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4313 (p : Pattern) (guard : d62765 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2614 p = 1 := by simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4312 p hg
    simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4314 (p : Pattern) (guard : d62766 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62765 p = 1 := by simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4313 p hg
    simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4315 (p : Pattern) (guard : d62767 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62766 p = 1 := by simpa only [d62767, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d62767, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62767, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d62767, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4316 (p : Pattern) (guard : d62768 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62767 p = 1 := by simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4317 (p : Pattern) (guard : d62769 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62768 p = 1 := by simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4316 p hg
    simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4318 (p : Pattern) (guard : d62770 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62769 p = 1 := by simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4319 (p : Pattern) (guard : d62771 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62770 p = 1 := by simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4318 p hg
    simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4320 (p : Pattern) (guard : d62772 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62771 p = 1 := by simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4319 p hg
    simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4321 (p : Pattern) (guard : d62773 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62772 p = 1 := by simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4322 (p : Pattern) (guard : d62774 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62773 p = 1 := by simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4321 p hg
    simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4323 (p : Pattern) (guard : d62775 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62774 p = 1 := by simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4324 (p : Pattern) (guard : d62776 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62775 p = 1 := by simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4325 (p : Pattern) (guard : d62777 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62776 p = 1 := by simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4324 p hg
    simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4326 (p : Pattern) (guard : d62778 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d62764 p = 1 := by simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4311 p hg
    simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62777 p = 1 := by simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4325 p hg
    simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4327 (p : Pattern) (guard : d62779 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d62778 p = 1 := by simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4326 p hg
    simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4328 (p : Pattern) (guard : d62780 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d62779 p = 1 := by simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4327 p hg
    simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4329 (p : Pattern) (guard : d62781 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d62780 p = 1 := by simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4328 p hg
    simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4330 (p : Pattern) (guard : d62782 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d62781 p = 1 := by simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4329 p hg
    simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4331 (p : Pattern) (guard : d62783 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d62782 p = 1 := by simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4332 (p : Pattern) (guard : d62784 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d62783 p = 1 := by simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4331 p hg
    simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4333 (p : Pattern) (guard : d62785 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d62784 p = 1 := by simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4332 p hg
    simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4334 (p : Pattern) (guard : d62786 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d62785 p = 1 := by simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4333 p hg
    simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4335 (p : Pattern) (guard : d62787 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d62786 p = 1 := by simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4334 p hg
    simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4336 (p : Pattern) (guard : d62788 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d62787 p = 1 := by simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4335 p hg
    simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4337 (p : Pattern) (guard : d62789 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d62788 p = 1 := by simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4336 p hg
    simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4338 (p : Pattern) (guard : d62790 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d62789 p = 1 := by simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4337 p hg
    simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4339 (p : Pattern) (guard : d62791 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d62790 p = 1 := by simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4338 p hg
    simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4340 (p : Pattern) (guard : d62792 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d62791 p = 1 := by simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4339 p hg
    simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4341 (p : Pattern) (guard : d62793 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d62792 p = 1 := by simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4340 p hg
    simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4342 (p : Pattern) (guard : d62794 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d62793 p = 1 := by simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4341 p hg
    simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4343 (p : Pattern) (guard : d62795 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d62794 p = 1 := by simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4342 p hg
    simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4344 (p : Pattern) (guard : d62796 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d62795 p = 1 := by simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4343 p hg
    simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4345 (p : Pattern) (guard : d62797 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d62796 p = 1 := by simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4344 p hg
    simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4346 (p : Pattern) (guard : d62798 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d62797 p = 1 := by simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4345 p hg
    simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4347 (p : Pattern) (guard : d62799 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d62798 p = 1 := by simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4346 p hg
    simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4348 (p : Pattern) (guard : d62800 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d62799 p = 1 := by simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4347 p hg
    simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4349 (p : Pattern) (guard : d62801 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d62800 p = 1 := by simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4348 p hg
    simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4350 (p : Pattern) (guard : d62802 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d62801 p = 1 := by simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4349 p hg
    simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4351 (p : Pattern) (guard : d62803 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d62802 p = 1 := by simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4352 (p : Pattern) (guard : d62804 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d62803 p = 1 := by simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4351 p hg
    simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4353 (p : Pattern) (guard : d62805 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d62804 p = 1 := by simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4354 (p : Pattern) (guard : d62806 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d62805 p = 1 := by simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4353 p hg
    simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4355 (p : Pattern) (guard : d62807 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d62806 p = 1 := by simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4354 p hg
    simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4356 (p : Pattern) (guard : d62808 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d62807 p = 1 := by simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4355 p hg
    simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4357 (p : Pattern) (guard : d62809 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d62808 p = 1 := by simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4356 p hg
    simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4358 (p : Pattern) (guard : d62810 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d62809 p = 1 := by simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4357 p hg
    simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4359 (p : Pattern) (guard : d62811 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d62810 p = 1 := by simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4360 (p : Pattern) (guard : d62812 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d62811 p = 1 := by simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4359 p hg
    simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4361 (p : Pattern) (guard : d62813 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d62812 p = 1 := by simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4360 p hg
    simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4362 (p : Pattern) (guard : d62814 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d62813 p = 1 := by simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4363 (p : Pattern) (guard : d62815 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d62814 p = 1 := by simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4362 p hg
    simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4364 (p : Pattern) (guard : d62816 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d62815 p = 1 := by simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4363 p hg
    simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4365 (p : Pattern) (guard : d62817 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d62816 p = 1 := by simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4366 (p : Pattern) (guard : d62818 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d62817 p = 1 := by simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4367 (p : Pattern) (guard : d62819 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d62818 p = 1 := by simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4366 p hg
    simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4368 (p : Pattern) (guard : d62820 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d62819 p = 1 := by simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4367 p hg
    simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4369 (p : Pattern) (guard : d62821 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d62820 p = 1 := by simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4368 p hg
    simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4370 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-1 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4371 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-2 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4372 (p : Pattern) (guard : d4025 p = 1) : d47911 p ≤ (0 : Int) + d47911 p := by
  omega
theorem compare4373 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (-1 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4374 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (-2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4375 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4376 (p : Pattern) (guard : d75628 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4377 (p : Pattern) (guard : d69967 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4378 (p : Pattern) (guard : d77237 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4379 (p : Pattern) (guard : d81522 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4380 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4381 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4382 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4383 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4384 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4385 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4386 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d48115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4387 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d48115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4388 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d82346 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4389 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d82346 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4390 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d82402 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4391 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d82402 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4392 (p : Pattern) (guard : d82684 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4393 (p : Pattern) (guard : d83661 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4394 (p : Pattern) (guard : d72174 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4395 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d89607 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4396 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d89607 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4397 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4398 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4399 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4400 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4401 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4402 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (-1 : Int) + d47686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4403 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (-1 : Int) + d47693 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4404 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (-1 : Int) + d47690 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4405 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare4406 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4407 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4405 p hg
    simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4406 p hg
    simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4408 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4409 (p : Pattern) (guard : d16 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4407 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4410 (p : Pattern) (guard : d17 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4409 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4411 (p : Pattern) (guard : d18 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4410 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4412 (p : Pattern) (guard : d19 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4413 (p : Pattern) (guard : d20 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4412 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4414 (p : Pattern) (guard : d21 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4413 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4415 (p : Pattern) (guard : d22 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4414 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4416 (p : Pattern) (guard : d0 p = 1) : d47618 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4417 (p : Pattern) (guard : d23 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4415 p hg
    simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4418 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4419 (p : Pattern) (guard : d24 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4417 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4420 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4421 (p : Pattern) (guard : d25 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4419 p hg
    simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4422 (p : Pattern) (guard : d26 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4421 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4423 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4422 p hg
    simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4424 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4425 (p : Pattern) (guard : d28 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4423 p hg
    simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4426 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4427 (p : Pattern) (guard : d29 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4425 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4428 (p : Pattern) (guard : d30 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4427 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4429 (p : Pattern) (guard : d31 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4428 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4430 (p : Pattern) (guard : d32 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4431 (p : Pattern) (guard : d33 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4430 p hg
    simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4432 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4433 (p : Pattern) (guard : d34 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4431 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4434 (p : Pattern) (guard : d35 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4433 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4435 (p : Pattern) (guard : d36 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4434 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4436 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4437 (p : Pattern) (guard : d37 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4435 p hg
    simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4438 (p : Pattern) (guard : d38 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4437 p hg
    simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4439 (p : Pattern) (guard : d39 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4438 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4440 (p : Pattern) (guard : d40 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4439 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4441 (p : Pattern) (guard : d41 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4440 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4442 (p : Pattern) (guard : d42 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4441 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4443 (p : Pattern) (guard : d43 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4442 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4444 (p : Pattern) (guard : d44 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d43 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4443 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4445 (p : Pattern) (guard : d45 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d44 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4446 (p : Pattern) (guard : d46 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4445 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4447 (p : Pattern) (guard : d47 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4446 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4448 (p : Pattern) (guard : d48 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4449 (p : Pattern) (guard : d49 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4441 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4450 (p : Pattern) (guard : d50 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4451 (p : Pattern) (guard : d51 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d50 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4450 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4452 (p : Pattern) (guard : d52 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d51 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4451 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4453 (p : Pattern) (guard : d53 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d52 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4452 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4454 (p : Pattern) (guard : d54 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4455 (p : Pattern) (guard : d55 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d47 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4454 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4456 (p : Pattern) (guard : d56 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d48 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4448 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4455 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4457 (p : Pattern) (guard : d57 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d56 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4456 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4458 (p : Pattern) (guard : d58 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d57 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4457 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4459 (p : Pattern) (guard : d59 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d58 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4458 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4460 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4461 (p : Pattern) (guard : d0 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4462 (p : Pattern) (guard : d0 p = 1) : d47763 p ≤ (-1 : Int) + d47762 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4463 (p : Pattern) (guard : d0 p = 1) : d47746 p ≤ (-1 : Int) + d47756 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4464 (p : Pattern) (guard : d0 p = 1) : d47751 p ≤ (-1 : Int) + d47760 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4465 (p : Pattern) (guard : d0 p = 1) : d47734 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4466 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare4467 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4468 (p : Pattern) (guard : d15 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4466 p hg
    simpa only [d15, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d15, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4469 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4470 (p : Pattern) (guard : d16 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4468 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4471 (p : Pattern) (guard : d17 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4472 (p : Pattern) (guard : d18 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4473 (p : Pattern) (guard : d19 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4472 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4474 (p : Pattern) (guard : d20 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4475 (p : Pattern) (guard : d21 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4474 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4476 (p : Pattern) (guard : d22 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4477 (p : Pattern) (guard : d0 p = 1) : d47707 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4478 (p : Pattern) (guard : d23 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4476 p hg
    simpa only [d23, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d23, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4479 (p : Pattern) (guard : d0 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4480 (p : Pattern) (guard : d24 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4481 (p : Pattern) (guard : d0 p = 1) : d47661 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4482 (p : Pattern) (guard : d25 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4480 p hg
    simpa only [d25, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d25, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4483 (p : Pattern) (guard : d26 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4482 p hg
    simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4484 (p : Pattern) (guard : d27 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4483 p hg
    simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4485 (p : Pattern) (guard : d0 p = 1) : d47754 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4486 (p : Pattern) (guard : d28 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4484 p hg
    simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4487 (p : Pattern) (guard : d0 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4488 (p : Pattern) (guard : d29 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4486 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4489 (p : Pattern) (guard : d30 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4490 (p : Pattern) (guard : d31 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4491 (p : Pattern) (guard : d32 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d32, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d32, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4492 (p : Pattern) (guard : d33 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d33, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d33, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4493 (p : Pattern) (guard : d0 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4494 (p : Pattern) (guard : d34 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4492 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4495 (p : Pattern) (guard : d35 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4496 (p : Pattern) (guard : d36 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4497 (p : Pattern) (guard : d0 p = 1) : d47764 p ≤ (-1 : Int) + d47762 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4498 (p : Pattern) (guard : d37 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4496 p hg
    simpa only [d37, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d37, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4499 (p : Pattern) (guard : d38 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d38, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4498 p hg
    simpa only [d38, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
