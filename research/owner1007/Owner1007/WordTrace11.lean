import Owner1007.BudgetWords11
import NetHack.Sokoban.Reduction

namespace Owner1007.WordTrace11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.ZeroWord11 Owner1007.BudgetWords11 Owner1007.HeroLedger Owner1007.TokenAccounting

def Word (group : List Cell) (hero : Cell) : Prop :=
  ∃ i, i < 28 ∧ group = [cell i] ∧ hero ∈ region i

def Nonfill : Outcome → Prop
  | .push _ (.fill _) => False
  | _ => True

theorem projected_update (group : List Cell) (outcome : Outcome) :
    update group outcome = update group (GhostProjection.projectedOutcome group outcome) := by
  cases outcome with
  | walk _ => rfl
  | push source ending =>
    by_cases own : source ∈ group <;>
      simp only [GhostProjection.projectedOutcome,update,move,own,↓reduceIte]

theorem projected_hero (group : List Cell) (outcome : Outcome) :
    nextHero (GhostProjection.projectedOutcome group outcome) = nextHero outcome := by
  cases outcome with
  | walk _ => rfl
  | push source ending =>
    by_cases own : source ∈ group <;>
      simp only [GhostProjection.projectedOutcome,own,↓reduceIte,nextHero]

theorem projected_nonfill (group : List Cell) (outcome : Outcome) (safe : Nonfill outcome) :
    Nonfill (GhostProjection.projectedOutcome group outcome) := by
  cases outcome with
  | walk _ => trivial
  | push source ending =>
    cases ending with
    | fill _ => contradiction
    | stay _ =>
      by_cases own : source ∈ group <;>
        simp only [GhostProjection.projectedOutcome,own,↓reduceIte,Nonfill]

theorem nonfill_of_equal_holes {state : State} {t : Transition} {outcome : Outcome}
    (effect : Matches state t outcome) (same : t.state.holes = state.holes) : Nonfill outcome := by
  cases outcome with
  | walk _ => trivial
  | push source ending =>
    cases ending with
    | stay _ => trivial
    | fill hole =>
      have length := List.length_erase_of_mem effect.2.1
      have positive := List.length_pos_of_mem effect.2.1
      have equality := congrArg List.length same
      rw [effect.2.2] at equality
      change (state.holes.erase hole).length = state.holes.length at equality
      change False
      omega

theorem successor_bound (i : Nat) (active : i < 28) : successor i < 28 := by
  unfold successor
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split <;> omega

theorem next_word (i : Nat) (active : i < 28)
    {state : State} {t : Transition} {outcome : Outcome}
    (effect : Matches state t outcome) (safe : Nonfill outcome)
    (next : Next i (GhostProjection.projectedOutcome [cell i] outcome)) :
    Word (update [cell i] outcome) t.state.player := by
  have afterGroup := projected_update [cell i] outcome
  have afterHero : t.state.player = nextHero (GhostProjection.projectedOutcome [cell i] outcome) :=
    (matches_hero state t outcome effect).trans (projected_hero [cell i] outcome).symm
  cases shadowEq : GhostProjection.projectedOutcome [cell i] outcome with
  | walk target =>
    have inside : target ∈ region i := by simpa only [shadowEq,Next] using next
    refine ⟨i,active,?_,?_⟩
    · simpa only [shadowEq,update] using afterGroup
    · rw [afterHero,shadowEq]
      exact inside
  | push source ending =>
    cases ending with
    | fill hole =>
      have impossible := projected_nonfill [cell i] outcome safe
      simp only [shadowEq,Nonfill] at impossible
    | stay landing =>
      have data : source = cell i ∧ i ≠ 23 ∧ landing = cell (successor i) ∧ source ∈ region (successor i) := by
        simpa only [shadowEq,Next] using next
      refine ⟨successor i,successor_bound i active,?_,?_⟩
      · have projectedEq : update [cell i] (GhostProjection.projectedOutcome [cell i] outcome) =
            [cell (successor i)] := by
          rw [shadowEq,data.1]
          simp [update,move,post,data.2.2.1]
        exact afterGroup.trans projectedEq
      · rw [afterHero,shadowEq]
        exact data.2.2.2

theorem energy_cons (value : State → List Cell → Int) (credits : Cell → Int)
    (state middle final : State) (group : List Cell) (outcome : Outcome) (outcomes : List Outcome) :
    HeroLedger.energy value credits state final group (outcome :: outcomes) =
      charge credits group outcome + value middle (update group outcome) - value state group +
        HeroLedger.energy value credits middle final (update group outcome) outcomes := by
  simp only [HeroLedger.energy, HeroLedger.charges, endGroup]
  omega

theorem small_energy_word {invariant : State → Prop}
    (cert : GroupCertificate soko1_1.board 1 invariant)
    (frame : ∀ state group, state.holes = soko1_1.initial.holes →
      cert.groupValue state group = value0 state group)
    (credits : cert.holeWeight = NetHack.Soko11Hero315.holeWeight)
    {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
    {history : List Dir} {previousPushes previousMoves : Nat}
    (reached : Trace soko1_1.board soko1_1.initial history state previousPushes previousMoves)
    (good : invariant state)
    (holes : state.holes = soko1_1.initial.holes)
    (finalHoles : final.holes = soko1_1.initial.holes)
    (i : Nat) (active : i < 28) (present : cell i ∈ state.boulders)
    (inside : state.player ∈ region i)
    (cheap : HeroLedger.energy cert.groupValue cert.holeWeight state final [cell i] outcomes < 2) :
    Word (endGroup [cell i] outcomes) final.player := by
  induction logged generalizing history previousPushes previousMoves i with
  | nil current => exact ⟨i,active,rfl,inside⟩
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have down : t.state.holes.Sublist soko1_1.initial.holes := by
      simpa only [holes] using step_holes_sublist soko1_1.board state dir t head
    have up : soko1_1.initial.holes.Sublist t.state.holes := by
      simpa only [finalHoles] using tail.trace.holes_sublist
    have nextHoles : t.state.holes = soko1_1.initial.holes := down.eq_of_length_le up.length_le
    have safe := nonfill_of_equal_holes effect (nextHoles.trans holes.symm)
    have subset : [cell i] ⊆ state.boulders := by simpa using present
    have nextGood := cert.preserved state dir t good head
    have nextActual := step_boulders_nodup soko1_1.board state dir t (cert.unique state good) head
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual [cell i] (by simp) subset
    have nextSubset := GhostSubset.update_subset state t outcome effect [cell i] (by simp) subset
    have nextBound : (update [cell i] outcome).length ≤ 1 :=
      Nat.le_trans (update_length [cell i] outcome) (by simp)
    have tailNonnegative := HeroLedger.Logged.energy_nonnegative tail cert nextGood
      (update [cell i] outcome) nextUnique nextSubset nextBound
    have one := cert.row state dir t outcome [cell i] good (by simp) subset (by simp) head effect
    have decomposition := energy_cons cert.groupValue cert.holeWeight state t.state final [cell i] outcome outcomes
    have rawGap :
        charge cert.holeWeight [cell i] outcome +
          cert.groupValue t.state (update [cell i] outcome) - cert.groupValue state [cell i] =
        singleSlack state.player (cell i) (GhostProjection.projectedOutcome [cell i] outcome) := by
      rw [credits,frame t.state (update [cell i] outcome) nextHoles,frame state [cell i] holes]
      exact singleton_gap effect (cell i)
    have firstCheap :
        singleSlack state.player (cell i) (GhostProjection.projectedOutcome [cell i] outcome) < 2 := by
      rw [rawGap] at decomposition
      omega
    have restCheap :
        HeroLedger.energy cert.groupValue cert.holeWeight t.state final (update [cell i] outcome) outcomes < 2 := by
      omega
    have next := real_cheap_from_reached i active reached present holes head effect inside firstCheap
    obtain ⟨j,nextActive,groupEq,nextHero⟩ := next_word i active effect safe next
    have nextPresent : cell j ∈ t.state.boulders := nextSubset (by rw [groupEq]; simp)
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    rw [groupEq] at restCheap
    have result := ih nextReached nextGood nextHoles finalHoles j nextActive nextPresent nextHero restCheap
    simpa only [endGroup,groupEq] using result

#print axioms small_energy_word
end Owner1007.WordTrace11
