import Owner1007.PricedCorral
import Owner1007.RightEnergy12

namespace Owner1007.RightPrice4
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def pocket : List Cell := [115,116,117,142,143,169]
def locks : Fin 7 → List Cell
 | 0 => [141,168,246,271]
 | 1 => [141,168,271]
 | 2 => [141,168,246]
 | 3 => [115,246,271]
 | 4 => [142,246,271]
 | 5 => [169,246,271]
 | 6 => []
def region (i : Fin 7) : List Cell :=
 soko1_2.board.floor.filter fun c => !(locks i).contains c && (if i.val < 3 then !pocket.contains c else true)
def credit (i : Fin 7) : Int := if i.val=0 then 2 else if i.val=6 then 0 else 1

/-- A finite priced cut charged only to a persistent original-token subset.
A foreign original push is a zero-cost shadow walk. -/
theorem owned_step_price {n : Nat} {board : Board} {holes : List Cell} {potential : Potential}
    {K R : Fin n → List Cell} {C : Fin n → Int}
    (closed : PricedCorral.Closed board holes potential K R C)
    (Kunique : ∀ i, (K i).Nodup) (valid : Valid board potential)
    (state : State) (unique : state.boulders.Nodup) (holesInside : state.holes ⊆ holes)
    (disjoint : ∀ c ∈ state.boulders, c ∉ state.holes)
    (group : List Cell) (groupUnique : group.Nodup) (subset : group ⊆ state.boulders)
    {i : Fin n} (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group)
    (dir : Dir) (t : Transition) (checked : step board state dir = some t)
    (outcome : Outcome) (effect : Matches state t outcome) :
    ∃ j : Fin n, t.state.player ∈ R j ∧ K j ⊆ update group outcome ∧
      C i ≤ slack potential (projectedOutcome group outcome) + C j := by
  let shadow : State := ⟨state.player,group,state.holes⟩
  have physical := step_player_clear board state dir t checked
  have clear : state.player ∉ group := fun h => physical.2.2.1 (subset h)
  have standing : standingAllowed board shadow = true := by
    simp [standingAllowed,shadow,physical.1,physical.2.1,clear,physical.2.2.2]
  have active : goal shadow = false := by
    have core : exposedStep board state dir = some t := (exposedStep_eq board state dir).trans checked
    cases ongoing : goal state with
    | false => exact ongoing
    | true => simp [exposedStep,ongoing] at core
  have oracle := original_matches_shadow board state group unique subset disjoint dir t checked outcome effect
  obtain ⟨u,shadowStep,shadowEffect⟩ := oracle_realized board shadow groupUnique standing active dir
    (projectedOutcome group outcome) oracle
  have good : PricedCorral.Good K R i shadow := ⟨heroInside,locksInside⟩
  obtain ⟨j,nextGood,price⟩ := PricedCorral.step_price closed Kunique valid good holesInside shadowStep
  have delta := matches_delta potential shadow u (projectedOutcome group outcome) shadowEffect
  have boxes : u.state.boulders = update group outcome := by
    have h := GhostOracleFacts.matches_update shadow u _ shadowEffect
    change u.state.boulders = update group (projectedOutcome group outcome) at h
    exact h.trans (RawGhostBonus.update_projected group outcome)
  have hero : u.state.player = t.state.player :=
    (HazardPattern.matches_hero shadow u _ shadowEffect).trans
      ((RawGhostBonus.hero_projected group outcome).trans
        (HazardPattern.matches_hero state t outcome effect).symm)
  refine ⟨j,?_,?_,?_⟩
  · simpa only [hero] using nextGood.1
  · simpa only [boxes] using nextGood.2
  · omega

theorem owned_trace_price {n : Nat}
    {K R : Fin n → List Cell} {C : Fin n → Int}
    (closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p K R C)
    (Kunique : ∀ i, (K i).Nodup)
    {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    {i : Fin n} (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group) :
    ∃ j : Fin n, final.player ∈ R j ∧ K j ⊆ endGroup group outcomes ∧
      C i ≤ ownSlack p group outcomes + C j := by
  induction logged generalizing history past pastMoves group i with
  | nil current => exact ⟨i,heroInside,locksInside,by simp only [ownSlack,Int.zero_add]; exact Int.le_refl _⟩
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    obtain ⟨j,nextHero,nextInside,one⟩ := owned_step_price closed Kunique
      Generated.soko1_2_potential_valid state actualUnique reached.holes_sublist.subset
      (RightEnergy12.trace_disjoint reached RightEnergy12.initial_disjoint)
      group unique subset heroInside locksInside dir t head outcome effect
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
    have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    obtain ⟨k,finalHero,finalInside,later⟩ := ih nextReached (update group outcome) nextUnique nextSubset
      nextHero nextInside
    refine ⟨k,finalHero,finalInside,?_⟩
    simp only [ownSlack]
    omega

def matrixNode (i : Fin 7) : Bool :=
  (region i).all fun hero => allDirs.all fun dir =>
    Corral11.walkCheck soko1_2.board locks region i hero dir &&
      PricedCorral.pushCheck soko1_2.board soko1_2.initial.holes p locks region credit i hero dir

#print axioms owned_step_price
end Owner1007.RightPrice4
