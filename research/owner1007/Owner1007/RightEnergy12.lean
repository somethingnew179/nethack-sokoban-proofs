import Owner1007.TokenPersistence
import NetHack.Sokoban.Reduction
import NetHack.Sokoban.RawGhostBonus
import NetHack.Sokoban12CostPartition.LowerBound

namespace Owner1007.RightEnergy12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open NetHack.Sokoban.PatternCorrection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem roll_unfilled_not_hole (board : Board) (stationary holes : List Cell) (dir : Dir)
    (fuel current : Nat) (result : PushResult) (clear : current ∉ holes)
    (checked : roll board stationary holes dir fuel current = some result)
    (unfilled : result.filled = none) : result.landing ∉ holes := by
  induction fuel generalizing current result with
  | zero => simp [roll] at checked
  | succ fuel ih =>
    cases adjacent : advance board current dir with
    | none =>
      simp [roll,adjacent] at checked
      subst result
      exact clear
    | some next =>
      by_cases door : next ∈ board.doors
      · simp [roll,adjacent,door] at checked
      · by_cases floor : next ∈ board.floor
        · by_cases collision : next ∈ stationary
          · simp [roll,adjacent,door,floor,collision] at checked
          · by_cases hazard : next ∈ holes
            · simp [roll,adjacent,door,floor,collision,hazard] at checked
              subst result
              simp at unfilled
            · simp [roll,adjacent,door,floor,collision,hazard] at checked
              exact ih next result hazard checked unfilled
        · simp [roll,adjacent,door,floor] at checked
          subst result
          exact clear

theorem push_unfilled_not_hole (board : Board) (state : State) (source : Cell)
    (dir : Dir) (result : PushResult)
    (checked : pushBoulder board state source dir = some result)
    (unfilled : result.filled = none) : result.landing ∉ state.holes := by
  obtain ⟨destination,adjacent,floor,door,clear⟩ := NonlinearFacts.pushBoulder_first_clear board state source dir result checked
  have remaining : destination ∉ state.boulders.erase source := fun h => clear (List.mem_of_mem_erase h)
  cases diagonal : dir.diagonal with
  | true => simp [pushBoulder,diagonal] at checked
  | false =>
    cases support : advance board source dir.opposite with
    | none => simp [pushBoulder,diagonal,support] at checked
    | some behind =>
      by_cases hazard : destination ∈ state.holes
      · simp [pushBoulder,diagonal,support,adjacent,floor,door,clear,hazard] at checked
        have same := checked.2
        subst result
        simp at unfilled
      · by_cases rolling : destination ∈ board.rollingTraps
        · simp [pushBoulder,diagonal,support,adjacent,floor,door,clear,hazard,rolling] at checked
          have rolled := checked.2
          simp [roll,adjacent,floor,door,remaining,hazard] at rolled
          exact roll_unfilled_not_hole board (state.boulders.erase source) state.holes dir
            (board.width * board.height) destination result hazard rolled unfilled
        · simp [pushBoulder,diagonal,support,adjacent,floor,door,clear,hazard,rolling] at checked
          have same := checked.2
          subst result
          exact hazard

def Disjoint (state : State) : Prop := ∀ c ∈ state.boulders, c ∉ state.holes

theorem step_disjoint {board : Board} {state : State} {dir : Dir} {t : Transition}
    (before : Disjoint state) (checked : step board state dir = some t) : Disjoint t.state := by
  have holesSubset := (step_holes_sublist board state dir t checked).subset
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target,_,_,_,_,shape⟩ := walked
    simpa only [Disjoint,shape] using before
  · obtain ⟨source,result,_,_,_,push,shape⟩ := pushed
    rcases (pushBoulder_spec board state source dir result push).1 with stay | fill
    · obtain ⟨unfilled,boxes⟩ := stay
      have landingClear := push_unfilled_not_hole board state source dir result push unfilled
      intro c member hole
      have oldHole := holesSubset hole
      rw [shape] at member
      change c ∈ result.boulders at member
      rw [boxes] at member
      rcases List.mem_cons.mp member with same | later
      · exact landingClear (same ▸ oldHole)
      · exact before c (List.mem_of_mem_erase later) oldHole
    · intro c member hole
      have oldHole := holesSubset hole
      rw [shape] at member
      change c ∈ result.boulders at member
      rw [fill.2.2] at member
      exact before c (List.mem_of_mem_erase member) oldHole

theorem trace_disjoint {board initial final dirs pushes moves}
    (trace : Trace board initial dirs final pushes moves) (before : Disjoint initial) : Disjoint final := by
  induction trace with
  | nil => exact before
  | cons head tail ih => exact ih (step_disjoint before head)

abbrev raw := Generated.soko1_2Potential
abbrev cert := NetHack.Sokoban12CostPartition.certificate

theorem initial_disjoint : Disjoint soko1_2.initial := by
  unfold Disjoint
  decide +kernel

theorem raw_group_energy {state final : State} {dirs : List Dir} {pushes moves : Nat}
    {outcomes : List Outcome}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final) :
    cert.bonus state.player (project group) ≤ energy raw group outcomes := by
  induction logged generalizing history past pastMoves group with
  | nil current =>
    have conserved := reached.conservation
    have empty : current.holes = [] := completed
    change 20 + current.holes.length = current.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    have count := List.Nodup.length_le_of_subset unique subset
    have small : group.length ≤ cert.allowance := by change group.length ≤ 2; omega
    have bound := RawPatternBonus.raw_goal cert Generated.soko1_2_potential_valid current.player group small
    change cert.bonus current.player (project group) ≤ debtOf raw group at bound
    simpa only [energy,ownSlack,endGroup,Int.zero_add] using bound
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
    have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    have one := RawGhostBonus.step_charge cert state actualUnique reached.holes_sublist.subset
      (trace_disjoint reached initial_disjoint) group unique subset dir t head outcome effect
    have later := ih nextReached (update group outcome) nextUnique nextSubset completed
    change cert.bonus state.player (project group) ≤
      slack raw (projectedOutcome group outcome) + cert.bonus t.state.player (project (update group outcome)) at one
    rw [energy_cons]
    omega

def Right : List Cell := [141,168,192,193,218,246,271]
theorem initial_right_bonus : cert.bonus soko1_2.initial.player (project Right) = 3 := by decide +kernel

/-- A disjoint right-token reservation valid for every original completion. -/
theorem right_energy_three {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) : 3 ≤ energy raw Right outcomes := by
  have bound := raw_group_energy logged (Trace.nil _) Right (by decide +kernel) (by decide +kernel) completed
  rw [initial_right_bonus] at bound
  exact bound

#print axioms trace_disjoint
#print axioms right_energy_three
end Owner1007.RightEnergy12
