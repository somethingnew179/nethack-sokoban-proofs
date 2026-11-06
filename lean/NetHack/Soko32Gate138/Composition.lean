/- Extend the already verified136 certificate by a gate credit. The old
bonus is unchanged on every transition which spends the new two-unit credit.
Thus push slack is spent once; two arbitrary lower bounds are NOT added. -/
import NetHack.Soko32Gate138.Checked
namespace NetHack.Soko32Gate138
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection NetHack.Sokoban.LowerBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def support : List Cell := prior.support ++ [165,244]
def bonus (hero : Cell) (p : Pattern) : Int := prior.bonus hero p + gate hero p
theorem old_subset : prior.support ⊆ support := fun _ member => List.mem_append.mpr (Or.inl member)
theorem gate_subset : gateSupport ⊆ support := by
  intro cell member
  have choices : cell = 139 ∨ cell = 165 ∨ cell = 244 := by simpa [gateSupport] using member
  rcases choices with rfl|rfl|rfl <;> decide +kernel

theorem old_hero_same (hero : Cell) (p : Pattern) (member : hero ∈ ([243,245,270] : List Cell)) :
    prior.bonus hero p = prior.bonus 244 p := by
  change NetHack.Sokoban32Refined.bonus hero p = NetHack.Sokoban32Refined.bonus 244 p
  have choices : hero = 243 ∨ hero = 245 ∨ hero = 270 := by simpa using member
  rcases choices with rfl|rfl|rfl
  · rw [NetHack.Sokoban32Refined.at243,NetHack.Sokoban32Refined.at244]
  · rw [NetHack.Sokoban32Refined.at245,NetHack.Sokoban32Refined.at244]
  · rw [NetHack.Sokoban32Refined.at270,NetHack.Sokoban32Refined.at244]
theorem old_pattern_same (p : Pattern) (landing : Cell) (outside : landing ∉ prior.support) :
    prior.bonus 244 p = prior.bonus 244 (change p 244 (some landing)) := by
  change NetHack.Sokoban32Refined.bonus 244 p = NetHack.Sokoban32Refined.bonus 244 (change p 244 (some landing))
  apply NetHack.Sokoban32Refined.respects
  intro cell member
  have sourceOutside : 244 ∉ prior.support := by decide +kernel
  have sourceNe : 244 ≠ cell := by intro same; exact sourceOutside (same ▸ member)
  have landingNe : landing ≠ cell := by intro same; exact outside (same ▸ member)
  simp [change,sourceNe,landingNe]

theorem sum_append (weight : Cell → Int) (a b : List Cell) :
    weightSum weight (a ++ b) = weightSum weight a + weightSum weight b := by
  induction a with
  | nil => simp [weightSum]
  | cons head tail ih => simp only [List.cons_append,weightSum_cons,ih]; omega
theorem gate_goal (hero : Cell) (p : Pattern) :
    gate hero p ≤ weightSum (fun cell => -potential.boulder cell) (([165,244] : List Cell).filter p) := by
  have zero : -potential.boulder 165 = 0 := by decide +kernel
  have sixteen : -potential.boulder 244 = 16 := by decide +kernel
  have sum : weightSum (fun cell => -potential.boulder cell) (([165,244] : List Cell).filter p) =
      (if p 244 then (16 : Int) else 0) := by
    cases a : p 165 <;> cases b : p 244 <;> simp [a,b,weightSum,zero,sixteen]
  rw [sum]
  cases b : p 244 with
  | false => simp [gate,b]
  | true => have cap := gate_at_most_two hero p; simp only [b,↓reduceIte]; omega

def certificate : Certificate soko3_2.board soko3_2.initial.holes potential where
  allowance := prior.allowance
  support := support
  unique := by decide +kernel
  bonus := bonus
  nonnegative := by
    intro hero p
    have a := prior.nonnegative hero p
    have b := gate_nonnegative hero p
    unfold bonus; omega
  walk := by
    intro hero floor direction target adjacent targetFloor p guard
    have oldGuard := walkGuard_weaken _ prior.support support old_subset p hero target direction guard
    have smallGuard := walkGuard_weaken _ gateSupport support gate_subset p hero target direction guard
    have a := prior.walk hero floor direction target adjacent targetFloor p oldGuard
    have b := row_walk (gate_rows hero floor p) direction target adjacent targetFloor smallGuard
    unfold bonus; omega
  stay := by
    intro hero floor direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target p guard
    have oldGuard := pushGuard_weaken prior.support support old_subset p hero source first landing guard
    have smallGuard := pushGuard_weaken gateSupport support gate_subset p hero source first landing guard
    have a := prior.stay hero floor direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target p oldGuard
    by_cases mono : gate hero p ≤ gate source (change p source (some landing))
    · unfold bonus; dsimp only [potential] at *; omega
    · have numeric := row_stay (gate_rows hero floor p) direction source first landing
        diagonal adjacent sourceFloor firstAdj firstFloor target smallGuard
      have decreasing : gate source (change p source (some landing)) < gate hero p := by omega
      have sourceEq := fall_source hero p source landing numeric decreasing
      subst source
      have positive : 0 < gate hero p := by have h := gate_nonnegative 244 (change p 244 (some landing)); omega
      have frame := strict_frame hero floor direction adjacent diagonal (gate_positive_outside hero p positive) landing target
      have same := (old_hero_same hero p frame.1).trans (old_pattern_same p landing frame.2.1)
      have before := gate_at_most_two hero p
      have after := gate_nonnegative 244 (change p 244 (some landing))
      unfold bonus
      rw [same]
      dsimp only [potential] at *
      omega
  consume := by
    intro hero floor direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target hole p guard
    have oldGuard := pushGuard_weaken prior.support support old_subset p hero source first landing guard
    have smallGuard := pushGuard_weaken gateSupport support gate_subset p hero source first landing guard
    have a := prior.consume hero floor direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target hole p oldGuard
    have numeric := row_consume (gate_rows hero floor p) direction source first landing
      diagonal adjacent sourceFloor firstAdj firstFloor target hole smallGuard
    have sourceOther : source ≠ 244 := by
      intro same
      subst source
      exact no244_fill direction landing target hole
    have own : localPotential.boulder source = 0 := by simp [localPotential,sourceOther]
    have h0 : localPotential.hole landing = 0 := rfl
    rw [own,h0] at numeric
    have before := gate_cases hero p
    have after := gate_cases source (change p source none)
    have mono : gate hero p ≤ gate source (change p source none) := by omega
    unfold bonus; dsimp only [potential] at *; omega
  goal := by
    intro hero p budget
    have oldBudget : (prior.support.filter p).length ≤ prior.allowance := by
      change ((prior.support ++ [165,244]).filter p).length ≤ prior.allowance at budget
      simp only [List.filter_append,List.length_append] at budget
      omega
    have a := prior.goal hero p oldBudget
    have b := gate_goal hero p
    change bonus hero p ≤ weightSum (fun cell => -potential.boulder cell) (support.filter p)
    rw [support,List.filter_append,sum_append]
    unfold bonus
    dsimp only [potential] at *
    omega
end NetHack.Soko32Gate138
