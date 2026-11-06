/- Adding observed occupancy cells only strengthens the physical guards.
This is a logical relaxation lemma, not an assumption on original actions. -/
import NetHack.Sokoban.HeroPhasePotential.SmallPattern
namespace NetHack.Sokoban.PatternCorrection
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem neg_true_clear (bit : Bool) (h : (!bit) = true) : bit = false := by
  cases bit <;> simp_all

theorem known_support_mono (small large : List Cell) (subset : small ⊆ large)
    (p : Pattern) (cell : Cell) (found : known small p cell = true) : known large p cell = true := by
  rcases Bool.and_eq_true_iff.mp found with ⟨member,bit⟩
  exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (subset (List.contains_iff_mem.mp member)),bit⟩
theorem known_clear_weaken (small large : List Cell) (subset : small ⊆ large)
    (p : Pattern) (cell : Cell) (clear : known large p cell = false) : known small p cell = false := by
  cases found : known small p cell with
  | false => rfl
  | true =>
    have bad := known_support_mono small large subset p cell found
    rw [clear] at bad
    cases bad

theorem walkGuard_weaken (board : Board) (small large : List Cell) (subset : small ⊆ large)
    (p : Pattern) (hero target : Cell) (direction : Dir)
    (guard : walkGuard board large p hero target direction = true) :
    walkGuard board small p hero target direction = true := by
  have g := Bool.and_eq_true_iff.mp guard
  have pair := Bool.and_eq_true_iff.mp g.1
  have hc := known_clear_weaken small large subset p hero (neg_true_clear _ pair.1)
  have tc := known_clear_weaken small large subset p target (neg_true_clear _ pair.2)
  have bigCorner : HazardPattern.corner board (known large p) hero direction = false := neg_true_clear _ g.2
  have sc := HeroPhasePotential.corner_clear_mono board (known small p) (known large p)
    (fun cell found => known_support_mono small large subset p cell found) hero direction bigCorner
  change relaxedCorner board small p hero direction = false at sc
  simp only [walkGuard,hc,tc,sc,Bool.not_false,Bool.true_and]

theorem pushGuard_weaken (small large : List Cell) (subset : small ⊆ large)
    (p : Pattern) (hero source first landing : Cell)
    (guard : pushGuard large p hero source first landing = true) :
    pushGuard small p hero source first landing = true := by
  have g := Bool.and_eq_true_iff.mp guard
  have g3 := Bool.and_eq_true_iff.mp g.1
  have g2 := Bool.and_eq_true_iff.mp g3.1
  have hc := known_clear_weaken small large subset p hero (neg_true_clear _ g2.1)
  have fc := known_clear_weaken small large subset p first (neg_true_clear _ g3.2)
  have sourceSmall : (!small.contains source || known small p source) = true := by
    by_cases member : source ∈ small
    · have largeMember := subset member
      have present : known large p source = true := by simpa only [List.contains_iff_mem.mpr largeMember,Bool.not_true,Bool.false_or] using g2.2
      have bit := (Bool.and_eq_true_iff.mp present).2
      simp only [known,List.contains_iff_mem.mpr member,bit,Bool.not_true,Bool.true_and,Bool.false_or]
    · simp [member]
  have endpointSmall : (!known small p landing || decide (landing = source)) = true := by
    by_cases same : landing = source
    · simp [same]
    · have notKnown : (!known large p landing) = true := by simpa [same] using g.2
      have clear : known large p landing = false := neg_true_clear _ notKnown
      have smallClear := known_clear_weaken small large subset p landing clear
      simp only [smallClear,Bool.not_false,Bool.true_or]
  simp only [pushGuard,hc,fc,sourceSmall,endpointSmall,Bool.not_false,Bool.true_and]
end NetHack.Sokoban.PatternCorrection
