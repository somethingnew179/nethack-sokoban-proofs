/- Finite sparse credits over actual boulders. The selected list may omit
other boulders only because their scalar walk/phase changes are proved
nonnegative. No Model transition or boulder supply is changed. -/
import NetHack.Sokoban.HeroPhasePotential.Strict
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.HeroPhasePotential.SparseCredit
open NetHack.Sokoban LowerBounds HazardPattern
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf nextPhase)

theorem sum_transfer (cells selected : List Cell) (before after : Cell → Int)
    (left right : Int) (unique : cells.Nodup) (selectedUnique : selected.Nodup)
    (subset : selected ⊆ cells) (mono : ∀ box ∈ cells, before box ≤ after box)
    (localBound : weightSum before selected + left ≤ weightSum after selected + right) :
    weightSum before cells + left ≤ weightSum after cells + right := by
  induction selected generalizing cells left right with
  | nil =>
    have allMono := weightSum_mono cells before after mono
    simp only [weightSum] at localBound
    omega
  | cons first rest ih =>
    have present : first ∈ cells := subset List.mem_cons_self
    have a := weightSum_erase before cells first present
    have b := weightSum_erase after cells first present
    have selectedInfo := List.nodup_cons.mp selectedUnique
    have retained : rest ⊆ cells.erase first := by
      intro box member
      apply unique.mem_erase_iff.mpr
      refine ⟨?_,subset (List.mem_cons_of_mem _ member)⟩
      intro same
      apply selectedInfo.1
      simpa only [same] using member
    have erMono : ∀ box ∈ cells.erase first, before box ≤ after box := by
      intro box member
      exact mono box (unique.mem_erase_iff.mp member).2
    have nextLocal : weightSum before rest + (before first + left) ≤
        weightSum after rest + (after first + right) := by
      simp only [weightSum_cons] at localBound
      omega
    have bound := ih (cells.erase first) (before first + left) (after first + right)
      (unique.erase first) selectedInfo.2 retained erMono nextLocal
    omega

def localCondition {board original phases} (cert : Certificate board original phases)
    (phase hero : Nat) (selected : List Cell) (before after : Int) : Outcome → Prop
  | .walk target =>
      weightSum (cert.weight phase hero) selected + before ≤
        weightSum (cert.weight phase target) selected + after
  | .push source (.stay landing) =>
      cert.weight phase hero source + weightSum (cert.weight phase hero) selected + before ≤
        1 + cert.weight phase source landing + weightSum (cert.weight phase source) selected + after
  | .push source (.fill hole) =>
      cert.weight phase hero source + cert.holeWeight hole + weightSum (cert.weight phase hero) selected + before ≤
        1 + weightSum (cert.weight (phase+1) source) selected + after
instance {board original phases} (cert : Certificate board original phases)
    (phase hero : Nat) (selected : List Cell) (before after : Int) (outcome : Outcome) :
    Decidable (localCondition cert phase hero selected before after outcome) := by
  cases outcome with
  | walk _ => unfold localCondition; infer_instance
  | push _ result => cases result <;> unfold localCondition <;> infer_instance

def retained (state : State) : Outcome → List Cell
  | .walk _ => state.boulders
  | .push source _ => state.boulders.erase source

theorem step_credit_bound {board original phases} (cert : Certificate board original phases)
    (state : State) (direction : Dir) (t : Transition)
    (good : HazardPhases.Good phases state)
    (checked : step board state direction = some t)
    (outcome : Outcome) (effect : Matches state t outcome)
    (selected : List Cell) (selectedUnique : selected.Nodup)
    (subset : selected ⊆ retained state outcome)
    (before after : Int)
    (localBound : localCondition cert (phaseOf original state) state.player selected before after outcome) :
    value cert state + before ≤ Int.ofNat t.pushCost + value cert t.state + after := by
  have unique := good.1
  rcases good.2 with ⟨phase,atIndex⟩
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  have within : HazardPhases.At phases (phaseOf original state) state := by
    rw [←phaseEq]; exact atIndex
  let index := phaseOf original state
  have active : index < original.length :=
    HazardPhaseCountedCorrection.active_of_step phases state within direction t checked
  have standing := step_player_clear board state direction t checked
  have heroHole : state.player ∉ original.drop index := by
    rw [←within.2.1]; exact standing.2.2.2
  have clear := FiniteTopology.step_corner_clear board state direction t checked
  have scalarWalk (box : Cell) (member : box ∈ state.boulders) (target : Cell)
      (adjacent : advance board state.player direction = some target)
      (floor : target ∈ board.floor) (door : target ∉ board.doors)
      (hole : target ∉ state.holes) (different : target ≠ box) :
      cert.weight index state.player box ≤ cert.weight index target box := by
    have heroBox : state.player ≠ box := by
      intro same; apply standing.2.2.1; simpa only [same] using member
    have targetHole : target ∉ original.drop index := by rw [←within.2.1]; exact hole
    have smallCorner : corner board (PatternCorrection.project [box]) state.player direction = false :=
      (corner_project board (single state box) direction).trans
        (single_corner_clear board state box member direction clear)
    exact cert.walk index active state.player within.2.2.1 box (within.2.2.2 member)
      direction target standing.1 standing.2.1 heroHole heroBox adjacent floor door targetHole different smallCorner
  have targetInfo := step_target board state direction t checked
  have phaseAfter := HazardPhaseCountedCorrection.matches_phase phases state t within outcome effect
  cases outcome with
  | walk target =>
    change t = { state := { state with player := target }, pushed := false, filled := none, pushSource := none, landing := none } at effect
    have adjacent : advance board state.player direction = some target := by simpa only [effect] using targetInfo.1
    have floor : target ∈ board.floor := by simpa only [effect] using targetInfo.2.1
    have door : target ∉ board.doors := by simpa only [effect] using targetInfo.2.2
    have boxClear : target ∉ state.boulders := by
      rcases step_cases_full board state direction t checked with walked | pushed
      · rcases walked with ⟨z,a,_,b,_,shape⟩
        have eq : z = target := by simpa only [effect,Option.some.injEq] using a.symm.trans adjacent
        simpa only [eq] using b
      · rcases pushed with ⟨source,result,_,_,_,_,shape⟩
        have noPush : t.pushed = false := by rw [effect]
        have yesPush : t.pushed = true := by rw [shape]
        rw [noPush] at yesPush
        cases yesPush
    have holeClear : target ∉ state.holes := by
      have afterGood := HazardPhases.step_good phases state direction t good checked
      have stand := step_player_clear board state direction t checked
      rcases step_cases_full board state direction t checked with walked | pushed
      · rcases walked with ⟨z,a,_,_,b,shape⟩
        have eq : z = target := by simpa only [effect,Option.some.injEq] using a.symm.trans adjacent
        simpa only [eq] using b
      · rcases pushed with ⟨source,result,_,_,_,_,shape⟩
        have noPush : t.pushed = false := by rw [effect]
        have yesPush : t.pushed = true := by rw [shape]
        rw [noPush] at yesPush
        cases yesPush
    have mono := fun box member => scalarWalk box member target adjacent floor door holeClear (by
      intro same; apply boxClear; simpa only [same] using member)
    have total := sum_transfer state.boulders selected _ _ before after unique selectedUnique subset mono localBound
    change phaseOf original t.state = index at phaseAfter
    change valueAt cert index state + before ≤ Int.ofNat t.pushCost + valueAt cert (phaseOf original t.state) t.state + after
    rw [phaseAfter]
    have zero : t.pushCost = 0 := by rw [effect]; rfl
    rw [zero]
    rw [effect]
    change weightSum (cert.weight index state.player) state.boulders +
      weightSum cert.holeWeight state.holes + before ≤
      0 + (weightSum (cert.weight index target) state.boulders + weightSum cert.holeWeight state.holes) + after
    omega
  | push source result =>
    have present : source ∈ state.boulders := by cases result <;> exact effect.1
    have targetEq : t.state.player = source := by
      have eq := matches_hero state t (.push source result) effect
      cases result <;> exact eq
    have adjacent : advance board state.player direction = some source := by simpa only [targetEq] using targetInfo.1
    have floor : source ∈ board.floor := by simpa only [targetEq] using targetInfo.2.1
    have door : source ∉ board.doors := by simpa only [targetEq] using targetInfo.2.2
    have noHole : source ∉ state.holes := by
      rw [within.2.1]
      exact cert.crate_disjoint index (by omega) source (within.2.2.2 present)
    have oldBoxes := weightSum_erase (cert.weight index state.player) state.boulders source present
    have erasedMono (box : Cell) (member : box ∈ state.boulders.erase source) :
        cert.weight index state.player box ≤ cert.weight index source box := by
      have erased := unique.mem_erase_iff.mp member
      exact scalarWalk box erased.2 source adjacent floor door noHole erased.1.symm
    cases result with
    | stay landing =>
      have total := sum_transfer (state.boulders.erase source) selected _ _
        (cert.weight index state.player source + before)
        (1 + cert.weight index source landing + after)
        (unique.erase source) selectedUnique subset erasedMono (by
          change cert.weight index state.player source + weightSum (cert.weight index state.player) selected + before ≤ 1 + cert.weight index source landing + weightSum (cert.weight index source) selected + after at localBound
          omega)
      change phaseOf original t.state = index at phaseAfter
      change valueAt cert index state + before ≤ Int.ofNat t.pushCost + valueAt cert (phaseOf original t.state) t.state + after
      rw [phaseAfter]
      simp only [valueAt,effect.2,Transition.pushCost,↓reduceIte,Int.ofNat_eq_natCast,weightSum_cons]
      omega
    | fill hole =>
      have nextGood := HazardPhases.step_good phases state direction t good checked
      have nextWithin : HazardPhases.At phases (index+1) t.state := by
        rcases nextGood.2 with ⟨nextIndex,nextAt⟩
        have eq := HazardPhaseCountedCorrection.at_phase phases nextIndex t.state nextAt
        change phaseOf original t.state = index+1 at phaseAfter
        have same : nextIndex = index+1 := eq.trans phaseAfter
        simpa only [same] using nextAt
      have advancedMono (box : Cell) (member : box ∈ state.boulders.erase source) :
          cert.weight index state.player box ≤ cert.weight (index+1) source box := by
        have erased := unique.mem_erase_iff.mp member
        have oldInside := within.2.2.2 erased.2
        have nextInside := nextWithin.2.2.2 (by simpa only [effect.2.2] using member)
        have advanced := cert.advancePhase index active source floor door (by rw [←within.2.1]; exact noHole)
          box oldInside nextInside erased.1.symm
        exact Int.le_trans (erasedMono box member) advanced
      have total := sum_transfer (state.boulders.erase source) selected _ _
        (cert.weight index state.player source + cert.holeWeight hole + before) (1+after)
        (unique.erase source) selectedUnique subset advancedMono (by
          change cert.weight index state.player source + cert.holeWeight hole + weightSum (cert.weight index state.player) selected + before ≤ 1 + weightSum (cert.weight (index+1) source) selected + after at localBound
          omega)
      have oldHoles := weightSum_erase cert.holeWeight state.holes hole effect.2.1
      change phaseOf original t.state = index+1 at phaseAfter
      change valueAt cert index state + before ≤ Int.ofNat t.pushCost + valueAt cert (phaseOf original t.state) t.state + after
      rw [phaseAfter]
      simp only [valueAt,effect.2.2,Transition.pushCost,↓reduceIte,Int.ofNat_eq_natCast]
      omega
end NetHack.Sokoban.HeroPhasePotential.SparseCredit
