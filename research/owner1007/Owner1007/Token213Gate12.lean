import Owner1007.OwnedEventsMore12
import Owner1007.LockedTokens
namespace Owner1007.Token213Gate12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks : Fin 2 → List Cell | 0 => [213] | 1 => [212]
def region (i : Fin 2) : List Cell := soko1_2.board.floor.filter fun c => !(locks i).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
  (source=213 ∧ dir≠.west) ∨ source=212
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid = true := by
  decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem debt_two : ∀ i, 2 ≤ debtOf p (locks i) := by decide +kernel
theorem bad_price : ∀ source ∈ [213,212], ∀ dir ∈ allDirs,
    paid source dir → ¬ (source=212 ∧ dir=.north) →
    ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧ (2 : Int) ≤ 1 + p.boulder dest - p.boulder source := by decide +kernel
theorem hero238 : ∀ hero ∈ soko1_2.board.floor,
    advance soko1_2.board hero .north = some 212 → hero=238 := by decide +kernel

theorem cheap_crossing {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (hero : state.player ∈ region 0) (present : 213 ∈ state.boulders)
    (cheap : energy p [213] outcomes ≤ 1) :
    ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
      outcomes = before ++ .push 212 (.stay 186) :: after ∧
      Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
      step soko1_2.board middle .north = some t ∧ Matches middle t (.push 212 (.stay 186)) ∧
      Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
      middle.player=238 ∧ 238 ∉ middle.boulders ∧ 186 ∉ middle.boulders ∧
      endGroup [213] before = [212] := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
  have initialUnique := reached.boulders_nodup (by decide +kernel)
  have groupUnique : ([213] : List Cell).Nodup := by simp
  have subset : ([213] : List Cell) ⊆ state.boulders := by simpa using present
  rcases event_or_good closed unique logged reached [213] groupUnique subset hero (by simp [locks]) with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,heroBefore,inside,pays⟩ := event.split
    have middleReached := reached.append first.trace
    cases outcome with
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,isPaid⟩ := pays
      have eventBound := event_energy_le Generated.soko1_2_potential_valid [213] first last (.push source ending)
      simp only [projectedOutcome,if_pos owner] at eventBound
      have sourceInside : source ∈ ([213,212] : List Cell) := by
        rcases isPaid with h | h <;> simp_all
      have expected : source=212 ∧ dir=.north := by
        apply Classical.byContradiction
        intro wrong
        have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
          (bad_price source sourceInside dir (Geometry.all_directions dir) isPaid wrong) checked effect
        dsimp only [p] at cheap one
        rw [shape] at cheap
        omega
      obtain ⟨rfl,rfl⟩ := expected
      have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
        (show pushTargets soko1_2.board 212 .north = [186] by decide +kernel) (by decide +kernel) checked effect
      subst ending
      obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
      have physical := step_player_clear soko1_2.board middle .north t checked
      have at238 := hero238 middle.player physical.1 adjacent
      have firstClear := push_first_clear soko1_2.board middle 212 .north result push
      have no186 : 186 ∉ middle.boulders := by
        obtain ⟨dest,next,_,_,empty⟩ := firstClear.2
        have same : dest=186 := by
          have singleton : advance soko1_2.board 212 .north = some 186 := by decide +kernel
          rw [singleton] at next
          exact Option.some.inj next.symm
        simpa only [same] using empty
      have no238 : 238 ∉ middle.boulders := by simpa only [at238] using physical.2.2.1
      have count := endGroup_length_le [213] before
      have exactToken : endGroup [213] before = [212] := by
        cases cells : endGroup [213] before with
        | nil => simp only [cells,List.not_mem_nil] at owner
        | cons c rest =>
          have empty : rest=[] := List.eq_nil_of_length_eq_zero (by simp only [cells,List.length_cons,List.length_nil] at count; omega)
          rw [cells,empty] at owner
          have same : 212=c := List.mem_singleton.mp owner
          simp only [cells,empty,same]
      exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,t,after,afterDirs,afterPushes,afterMoves,
        shape,first,checked,effect,last,at238,no238,no186,exactToken⟩
  · obtain ⟨i,hero,inside⟩ := terminal
    have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -p.boulder c)
      (locks i) (endGroup [213] outcomes)
      (fun c => by have h := Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c ≤ 0 at h; omega)
      (unique i) inside
    change debtOf p (locks i) ≤ debtOf p (endGroup [213] outcomes) at debt
    have high := debt_two i
    have nonnegative := logged.ownSlack_nonnegative Generated.soko1_2_potential_valid [213]
    change 0 ≤ ownSlack p [213] outcomes at nonnegative
    unfold energy at cheap
    omega
#print axioms matrix
#print axioms cheap_crossing
end Owner1007.Token213Gate12
