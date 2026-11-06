/- With exactly one original hazard phase left, at most one member of a
two-boulder group can be consumed. Its group potential may use the minimum
of the two single weights, instead of their sum. This is a Model theorem,
not an assumption about which final spare boulders a solver chooses. -/
import NetHack.Sokoban.GhostNonlinear

namespace NetHack.Sokoban.GhostLastFill
open HazardPattern GhostPartition LowerBounds
open HazardPhaseCountedCorrection (phaseOf nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def single {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (state : State) (box : Cell) : Int := scalar.weight (phaseOf original state) state.player box
def base {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (state : State) (group : List Cell) : Int := weightSum (single scalar state) group
def value {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (state : State) (group : List Cell) : Int :=
  if original.length = phaseOf original state + 1 then
    match group with
    | [a,b] => min (single scalar state a) (single scalar state b)
    | _ => base scalar state group
  else base scalar state group

theorem min_bound (a b x y cost : Int) (left : a ≤ cost+x) (right : b ≤ cost+y) :
    min a b ≤ cost + min x y := by
  simp only [Int.min_def]
  split <;> split <;> omega

theorem dominates {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (nonpositive : ∀ phase hero box, scalar.weight phase hero box ≤ 0) (state : State) (group : List Cell) :
    base scalar state group ≤ value scalar state group := by
  unfold value
  split
  · cases group with
    | nil => exact Int.le_refl _
    | cons a rest =>
      cases rest with
      | nil => exact Int.le_refl _
      | cons b tail =>
        cases tail with
        | nil =>
          have wa := nonpositive (phaseOf original state) state.player a
          have wb := nonpositive (phaseOf original state) state.player b
          change single scalar state a + (single scalar state b + 0) ≤ min (single scalar state a) (single scalar state b)
          dsimp only [single] at *
          simp only [Int.min_def]
          split <;> omega
        | cons c rest => exact Int.le_refl _
  · exact Int.le_refl _

theorem terminal_zero {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (zero : ∀ hero box, scalar.weight original.length hero box = 0)
    (state : State) (group : List Cell) (last : phaseOf original state = original.length) :
    value scalar state group = 0 := by
  have unequal : ¬ original.length = phaseOf original state + 1 := by omega
  unfold value
  rw [if_neg unequal]
  unfold base single
  rw [last]
  induction group with
  | nil => rfl
  | cons first rest ih => rw [weightSum_cons,zero,ih]; rfl

theorem pair_last {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (state : State) (a b : Cell) (last : original.length = phaseOf original state + 1) :
    value scalar state [a,b] = min (single scalar state a) (single scalar state b) := by
  simp only [value,if_pos last]

theorem charge_stay_subset (holeWeight : Cell → Int) (small large : List Cell)
    (subset : small ⊆ large) (source landing : Cell) :
    charge holeWeight small (.push source (.stay landing)) ≤ charge holeWeight large (.push source (.stay landing)) := by
  by_cases member : source ∈ small
  · have present := subset member
    simp only [charge,if_pos member,if_pos present]
    exact Int.le_refl _
  · simp only [charge,if_neg member]
    split <;> omega

theorem stay_pair_value {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (state : State) (a b source landing : Cell) (different : a ≠ b)
    (last : original.length = phaseOf original state+1) :
    value scalar state (update [a,b] (.push source (.stay landing))) =
      min (base scalar state (update [a] (.push source (.stay landing))))
        (base scalar state (update [b] (.push source (.stay landing)))) := by
  by_cases sa : source = a
  · subst source
    simp [update,move,post,value,last,base,weightSum,different]
  · by_cases sb : source = b
    · subst source
      simp [update,move,post,value,last,base,weightSum,different,Ne.symm different,Int.min_comm]
    · simp [update,move,post,value,last,base,weightSum,sa,sb]

def asOriginalCertificate {board original phases}
    (scalar : HeroPhasePotential.Certificate board original phases)
    (nonpositive : ∀ phase hero box, scalar.weight phase hero box ≤ 0)
    (zero : ∀ hero box, scalar.weight original.length hero box = 0) :
    GroupCertificate board 2 (HazardPhases.Good phases) where
  groupValue := value scalar
  holeWeight := scalar.holeWeight
  unique := fun _ good => good.1
  preserved := HazardPhases.step_good phases
  row := by
    intro state direction t outcome group good unique inside length checked effect
    let baseline := GhostPhaseCertificate.asOriginalCertificate (GhostScalar.asOracleCertificate scalar 2)
    have old := baseline.row state direction t outcome group good unique inside length checked effect
    change base scalar state group ≤ charge scalar.holeWeight group outcome +
      base scalar t.state (update group outcome) at old
    have afterDom := dominates scalar nonpositive t.state (update group outcome)
    by_cases unchanged : value scalar state group = base scalar state group
    · rw [unchanged]
      omega
    · have last : original.length = phaseOf original state+1 := by
        by_cases h : original.length = phaseOf original state+1
        · exact h
        · exact False.elim (unchanged (by simp [value,h]))
      cases group with
      | nil => exact False.elim (unchanged (by simp [value,last]))
      | cons a rest =>
        cases rest with
        | nil => exact False.elim (unchanged (by simp [value,last]))
        | cons b tail =>
          cases tail with
          | cons c rest => simp only [List.length_cons] at length; omega
          | nil =>
            have different : a ≠ b := by simpa using (List.nodup_cons.mp unique).1
            have aInside : [a] ⊆ state.boulders := by
              intro box member
              have same : box = a := by simpa using member
              subst box
              exact inside (by simp)
            have bInside : [b] ⊆ state.boulders := by
              intro box member
              have same : box = b := by simpa using member
              subst box
              exact inside (by simp)
            have firstA := baseline.row state direction t outcome [a] good (by simp) aInside (by simp) checked effect
            have firstB := baseline.row state direction t outcome [b] good (by simp) bInside (by simp) checked effect
            change base scalar state [a] ≤ charge scalar.holeWeight [a] outcome +
              base scalar t.state (update [a] outcome) at firstA
            change base scalar state [b] ≤ charge scalar.holeWeight [b] outcome +
              base scalar t.state (update [b] outcome) at firstB
            have rowA : single scalar state a ≤ charge scalar.holeWeight [a] outcome +
                base scalar t.state (update [a] outcome) := by simpa [base,weightSum] using firstA
            have rowB : single scalar state b ≤ charge scalar.holeWeight [b] outcome +
                base scalar t.state (update [b] outcome) := by simpa [base,weightSum] using firstB
            rcases good.2 with ⟨phase,atIndex⟩
            have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
            have within : HazardPhases.At phases (phaseOf original state) state := by rw [←phaseEq]; exact atIndex
            have afterPhase := HazardPhaseCountedCorrection.matches_phase phases state t within outcome effect
            rw [pair_last scalar state a b last]
            cases outcome with
            | walk target =>
              have nextLast : original.length = phaseOf original t.state+1 := by rw [afterPhase]; exact last
              simp only [charge,update,Int.zero_add] at rowA rowB ⊢
              rw [pair_last scalar t.state a b nextLast]
              simp only [base,weightSum,Int.add_zero] at rowA rowB
              simpa only [Int.zero_add] using min_bound _ _ _ _ 0
                (by simpa only [Int.zero_add] using rowA) (by simpa only [Int.zero_add] using rowB)
            | push source result =>
              cases result with
              | stay landing =>
                have nextLast : original.length = phaseOf original t.state+1 := by rw [afterPhase]; exact last
                rw [stay_pair_value scalar t.state a b source landing different nextLast]
                have ca := charge_stay_subset scalar.holeWeight [a] [a,b]
                  (by intro x h; exact List.mem_cons.mpr (Or.inl (by simpa using h))) source landing
                have cb := charge_stay_subset scalar.holeWeight [b] [a,b] (by intro x h; simp_all) source landing
                exact min_bound _ _ _ _ _ (by omega) (by omega)
              | fill hole =>
                have terminal : phaseOf original t.state = original.length := afterPhase.trans last.symm
                rw [terminal_zero scalar zero t.state _ terminal]
                by_cases owner : source ∈ [a,b]
                · have casesSource : source = a ∨ source = b := by simpa using owner
                  rcases casesSource with rfl|rfl
                  · simp [charge,update,move,post,base,weightSum,different] at rowA ⊢
                    exact Int.le_trans (Int.min_le_left _ _) rowA
                  · simp [charge,update,move,post,base,weightSum,different,Ne.symm different] at rowB ⊢
                    exact Int.le_trans (Int.min_le_right _ _) rowB
                · simp only [charge,if_neg owner,Int.add_zero]
                  exact Int.le_trans (Int.min_le_left _ _) (nonpositive _ _ a)
  terminal := by
    intro state group good completed unique inside length
    have last : phaseOf original state = original.length := by
      have empty : state.holes = [] := completed
      simp only [phaseOf,empty,List.length_nil,Nat.sub_zero]
    rw [terminal_zero scalar zero state group last]
    exact Int.le_refl 0

end NetHack.Sokoban.GhostLastFill
