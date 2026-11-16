import Owner1007.HeroLedger

namespace Owner1007.OwnedStrict11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)

def groupValue {board original phases}
    (cert : HeroPhasePotential.Certificate board original phases) (state : State) (group : List Cell) : Int :=
  weightSum (cert.weight (phaseOf original state) state.player) group

theorem owned_stay_bound {board original phases}
    (cert : HeroPhasePotential.Certificate board original phases)
    (state : State) (direction : Dir) (t : Transition)
    (good : HazardPhases.Good phases state) (checked : step board state direction = some t)
    (source landing : Cell) (effect : Matches state t (.push source (.stay landing)))
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ state.boulders)
    (owner : source ∈ group) (price : Int)
    (ownPrice : price ≤ 1 + cert.weight (phaseOf original state) source landing -
      cert.weight (phaseOf original state) state.player source) :
    price ≤ charge cert.holeWeight group (.push source (.stay landing)) +
      groupValue cert t.state (update group (.push source (.stay landing))) - groupValue cert state group := by
  obtain ⟨oldUnique, phase, atIndex⟩ := good
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  let index := phaseOf original state
  have within : HazardPhases.At phases index state := by
    change HazardPhases.At phases (phaseOf original state) state
    rw [←phaseEq]; exact atIndex
  have active : index < original.length :=
    HazardPhaseCountedCorrection.active_of_step phases state within direction t checked
  have standing := step_player_clear board state direction t checked
  have heroHole : state.player ∉ original.drop index := by
    rw [←within.2.1]; exact standing.2.2.2
  have scalarWalk (box : Cell) (member : box ∈ state.boulders) (target : Cell)
      (adjacent : advance board state.player direction = some target)
      (floor : target ∈ board.floor) (door : target ∉ board.doors)
      (hole : target ∉ state.holes) (different : target ≠ box) :
      cert.weight index state.player box ≤ cert.weight index target box := by
    have heroBox : state.player ≠ box := by
      intro same; apply standing.2.2.1; simpa only [same] using member
    have targetHole : target ∉ original.drop index := by rw [←within.2.1]; exact hole
    have singleton : [box] ⊆ state.boulders := by simpa using member
    have smallCorner := GhostProjection.original_corner_projected board state [box] singleton direction t checked
    exact cert.walk index active state.player within.2.2.1 box (within.2.2.2 member)
      direction target standing.1 standing.2.1 heroHole heroBox adjacent floor door targetHole different smallCorner
  have target := HeroPhasePotential.step_target board state direction t checked
  have adjacent : advance board state.player direction = some source := by simpa only [effect.2] using target.1
  have floor : source ∈ board.floor := by simpa only [effect.2] using target.2.1
  have door : source ∉ board.doors := by simpa only [effect.2] using target.2.2
  have noHole : source ∉ state.holes := by
    rw [within.2.1]
    exact cert.crate_disjoint index (by omega) source (within.2.2.2 effect.1)
  have before := weightSum_erase (cert.weight index state.player) group source owner
  have mono := HeroPhasePotential.weightSum_mono (group.erase source)
    (cert.weight index state.player) (cert.weight index source) (fun box member => by
      have erased := unique.mem_erase_iff.mp member
      exact scalarWalk box (inside erased.2) source adjacent floor door noHole erased.1.symm)
  have afterPhase := HazardPhaseCountedCorrection.matches_phase phases state t within
    (.push source (.stay landing)) effect
  change phaseOf original t.state = index at afterPhase
  change price ≤ 1 + cert.weight index source landing - cert.weight index state.player source at ownPrice
  change price ≤ charge cert.holeWeight group (.push source (.stay landing)) +
    weightSum (cert.weight (phaseOf original t.state) t.state.player) (update group (.push source (.stay landing))) -
      weightSum (cert.weight index state.player) group
  rw [afterPhase]
  simp only [charge,update,move,if_pos owner,post,effect.2,weightSum_cons]
  omega

#print axioms owned_stay_bound
end Owner1007.OwnedStrict11
