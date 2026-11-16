import Owner1007.LeftPair11
import Owner1007.LeftStrict11
import Owner1007.LeftDebt11
import Owner1007.OwnedCorralBound11
import Owner1007.Hero315Frame11
import Owner1007.PairStrict11

namespace Owner1007.LeftEnergy11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)
open Owner1007.TokenAccounting
open Owner1007.Hero315Frame11

theorem canonical_pair (group : List Cell) (unique : group.Nodup) (bounded : group.length ≤ 2)
    (inside : [186,212] ⊆ group) : group.Perm [186,212] := by
  have smallUnique : ([186,212] : List Cell).Nodup := by decide
  apply (List.perm_ext_iff_of_nodup unique smallUnique).mpr
  intro cell
  constructor
  · intro member
    by_cases known : cell ∈ [186,212]
    · exact known
    · have all : cell :: [186,212] ⊆ group := by
        intro c found
        rcases List.mem_cons.mp found with rfl | later
        · exact member
        · exact inside later
      have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨known,smallUnique⟩) all
      change 3 ≤ group.length at card
      omega
  · exact fun found => inside found

theorem push_landing {state : State} {dir : Dir} {t : Transition} {source : Cell}
    (checked : step soko1_1.board state dir = some t) (sourceEq : t.pushSource = some source) :
    ∃ landing, t.landing = some landing ∧ landing ∈ pushTargets soko1_1.board source dir := by
  rcases step_cases_full _ _ _ _ checked with walked | pushed
  · obtain ⟨target,_,_,_,_,shape⟩ := walked
    simp only [shape] at sourceEq
    contradiction
  · obtain ⟨other,result,_,_,_,push,shape⟩ := pushed
    have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
    subst other
    exact ⟨result.landing,by simp only [shape],(pushBoulder_spec _ _ _ _ _ push).2⟩

theorem priced : ∀ state dir t outcome group,
      HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
      group.Nodup → group ⊆ state.boulders → group.length ≤ 2 →
      step soko1_1.board state dir = some t → Matches state t outcome →
      OwnedCorral11.PaidStep LeftPair11.paid group dir t →
      2 ≤ charge (groupCertificate 2).holeWeight group outcome +
        (groupCertificate 2).groupValue t.state (update group outcome) -
        (groupCertificate 2).groupValue state group := by
  intro state dir t outcome group good unique inside bounded checked effect pays
  exact LeftStrict11.exit_row scalar rfl good checked effect unique inside pays

theorem after_first {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (checked : step soko1_1.board state dir = some t) (effect : Matches state t outcome)
    (unique : group.Nodup) (bounded : group.length ≤ 2)
    (good : OwnedCorral11.Good LeftPair11.cut0Locks LeftPair11.cut0Region state group)
    (pays : OwnedCorral11.PaidStep LeftPair11.cut0Paid group dir t) :
    OwnedCorral11.Good LeftPair11.locks LeftPair11.region t.state (update group outcome) ∧
      (groupCertificate 2).groupValue t.state (update group outcome) ≤ -(2 : Int) := by
  obtain ⟨i,heroInside,inside⟩ := good
  have canon := canonical_pair group unique bounded inside
  obtain ⟨source,owner,sourceEq,sources,dirEq⟩ := pays
  subst dir
  obtain ⟨phase,atIndex⟩ := valid.2
  have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
  have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate (phaseOf soko1_1.initial.holes state) state := by
    rw [←phaseEq]; exact atIndex
  have active := HazardPhaseCountedCorrection.active_of_step _ state within .west t checked
  have active16 : phaseOf soko1_1.initial.holes state < 16 := active
  have holesInside : state.holes ⊆ soko1_1.initial.holes := by
    rw [atIndex.2.1]
    exact (List.drop_sublist phase _).subset
  have bigExit : LeftActor11.Exit source .west := by
    rcases sources with rfl|rfl <;> simp [LeftActor11.Exit]
  obtain ⟨landing,landed,unfilled,_⟩ := LeftActor11.exit_price checked sourceEq bigExit holesInside
    (phaseOf soko1_1.initial.holes state) active16
  have same := PairStrict11.outcome_stay effect sourceEq landed unfilled
  subst outcome
  have afterPhase := HazardPhaseCountedCorrection.matches_phase _ state t within
    (.push source (.stay landing)) effect
  change phaseOf soko1_1.initial.holes t.state = phaseOf soko1_1.initial.holes state at afterPhase
  have hero : t.state.player=source := by simp only [effect.2]
  obtain ⟨actual,actualEq,target⟩ := push_landing checked sourceEq
  have actualLanding : actual=landing := by simpa only [Option.some.injEq] using actualEq.symm.trans landed
  rw [actualLanding] at target
  have nextPerm := update_perm canon (.push source (.stay landing))
  rcases sources with rfl | rfl
  · have destination : landing=185 := by
      have targets : pushTargets soko1_1.board 186 .west = [185] := by decide +kernel
      simpa only [targets,List.mem_singleton] using target
    rw [destination] at nextPerm ⊢
    constructor
    · refine ⟨⟨0,by decide⟩,?_,?_⟩
      · rw [hero]; decide +kernel
      · intro c found
        apply nextPerm.mem_iff.mpr
        simpa [LeftPair11.locks,update,move,post] using found
    · change weightSum (NetHack.Soko11Hero315.weight (phaseOf soko1_1.initial.holes t.state) t.state.player)
        (update group (.push 186 (.stay 185))) ≤ -2
      rw [afterPhase,hero]
      have sum := StatePermutation.weightSum_permutation
        (NetHack.Soko11Hero315.weight (phaseOf soko1_1.initial.holes state) 186) nextPerm
      rw [sum]
      simpa [update,move,post,weightSum] using (LeftDebt11.debts _ active16).1
  · have destination : landing=211 := by
      have targets : pushTargets soko1_1.board 212 .west = [211] := by decide +kernel
      simpa only [targets,List.mem_singleton] using target
    rw [destination] at nextPerm ⊢
    constructor
    · refine ⟨⟨1,by decide⟩,?_,?_⟩
      · rw [hero]; decide +kernel
      · intro c found
        apply nextPerm.mem_iff.mpr
        simpa [LeftPair11.locks,update,move,post,List.mem_cons,List.mem_singleton,or_comm] using found
    · change weightSum (NetHack.Soko11Hero315.weight (phaseOf soko1_1.initial.holes t.state) t.state.player)
        (update group (.push 212 (.stay 211))) ≤ -2
      rw [afterPhase,hero]
      have sum := StatePermutation.weightSum_permutation
        (NetHack.Soko11Hero315.weight (phaseOf soko1_1.initial.holes state) 212) nextPerm
      rw [sum]
      simpa [update,move,post,weightSum] using (LeftDebt11.debts _ active16).2

theorem first_unique (i : Fin 1) : (LeftPair11.cut0Locks i).Nodup := by
  change ([186,212] : List Cell).Nodup
  decide
theorem first_size (i : Fin 1) : (LeftPair11.cut0Locks i).length=2 := rfl

theorem post_energy
    (postClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LeftPair11.locks LeftPair11.region LeftPair11.paid)
    {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ state.boulders) (bounded : group.length ≤ 2)
    (good : OwnedCorral11.Good LeftPair11.locks LeftPair11.region state group)
    (holesInside : state.holes ⊆ soko1_1.initial.holes)
    (debt : (groupCertificate 2).groupValue state group ≤ -(2 : Int)) :
    2 ≤ energy state final group outcomes := by
  have groupSize : group.length=2 := by
    obtain ⟨i,_,subset⟩ := good
    have card := List.Nodup.length_le_of_subset (LeftPair11.unique i) subset
    rw [LeftPair11.size i] at card
    omega
  exact OwnedCorral11.energy_bound postClosed LeftPair11.unique LeftPair11.size (groupCertificate 2) 2
    priced logged valid group unique inside groupSize good holesInside debt (goal_value_zero completed _)

theorem bound_or_persist
    (firstClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LeftPair11.cut0Locks LeftPair11.cut0Region LeftPair11.cut0Paid)
    (postClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LeftPair11.locks LeftPair11.region LeftPair11.paid)
    {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ state.boulders) (bounded : group.length ≤ 2)
    (good : OwnedCorral11.Good LeftPair11.cut0Locks LeftPair11.cut0Region state group)
    (holesInside : state.holes ⊆ soko1_1.initial.holes) :
    4 ≤ energy state final group outcomes ∨
      OwnedCorral11.Good LeftPair11.cut0Locks LeftPair11.cut0Region final (endGroup group outcomes) := by
  induction logged generalizing group with
  | nil current => exact Or.inr good
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    let cert := groupCertificate 2
    have nextValid := cert.preserved state dir t valid head
    have nextActual := step_boulders_nodup _ _ _ _ (cert.unique state valid) head
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique inside
    have nextSubset := GhostSubset.update_subset state t outcome effect group unique inside
    have nextBound := Nat.le_trans (update_length group outcome) bounded
    have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
    have one := cert.row state dir t outcome group valid unique inside bounded head effect
    change value state group ≤ charge NetHack.Soko11Hero315.holeWeight group outcome + value t.state (update group outcome) at one
    have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final group outcome outcomes
    change Hero315Frame11.energy state final group (outcome :: outcomes) =
      charge NetHack.Soko11Hero315.holeWeight group outcome + value t.state (update group outcome) - value state group +
        Hero315Frame11.energy t.state final (update group outcome) outcomes at decomposition
    by_cases pays : OwnedCorral11.PaidStep LeftPair11.cut0Paid group dir t
    · have larger : OwnedCorral11.PaidStep LeftPair11.paid group dir t := by
        obtain ⟨source,owner,sourceEq,sources,dirEq⟩ := pays
        refine ⟨source,owner,sourceEq,?_⟩
        rcases sources with rfl|rfl <;> simp [LeftPair11.paid,dirEq]
      have firstCost := priced state dir t outcome group valid unique inside bounded head effect larger
      obtain ⟨postGood,debt⟩ := after_first valid head effect unique bounded good pays
      have later := post_energy postClosed tail completed nextValid (update group outcome)
        nextUnique nextSubset nextBound postGood nextHoles debt
      change 2 ≤ charge NetHack.Soko11Hero315.holeWeight group outcome + value t.state (update group outcome) - value state group at firstCost
      exact Or.inl (by omega)
    · have nextGood := OwnedCorral11.step_good_except firstClosed first_unique first_size good inside bounded holesInside head effect pays
      rcases ih completed nextValid (update group outcome) nextUnique nextSubset nextBound nextGood nextHoles with charged | persists
      · exact Or.inl (by omega)
      · exact Or.inr persists

theorem pair_energy
    (firstClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LeftPair11.cut0Locks LeftPair11.cut0Region LeftPair11.cut0Paid)
    (postClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LeftPair11.locks LeftPair11.region LeftPair11.paid)
    {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (completed : Goal final) :
    4 ≤ energy soko1_1.initial final [186,212] outcomes := by
  have initialGood : OwnedCorral11.Good LeftPair11.cut0Locks LeftPair11.cut0Region soko1_1.initial [186,212] := by
    refine ⟨⟨0,by decide⟩,?_,?_⟩ <;> decide +kernel
  rcases bound_or_persist firstClosed postClosed logged completed NetHack.SokobanLinearPhases.Map11.initial_good
      [186,212] (by decide) (by decide) (by decide) initialGood (by simp) with bound | persists
  · exact bound
  · obtain ⟨i,_,subset⟩ := persists
    have card := List.Nodup.length_le_of_subset (first_unique i) subset
    have upper := endGroup_length_le [186,212] outcomes
    have same : (endGroup [186,212] outcomes).length=([186,212] : List Cell).length := by
      rw [first_size i] at card
      simpa only [List.length_cons,List.length_nil] using Nat.le_antisymm upper card
    have ledger := HeroLedger.full_survivor_energy value NetHack.Soko11Hero315.holeWeight
      soko1_1.initial final [186,212] outcomes same (goal_value_zero completed _)
    have debt : value soko1_1.initial [186,212] ≤ -(4 : Int) := by decide +kernel
    have nonnegative : (0 : Int) ≤ Int.ofNat (ownPushes [186,212] outcomes) := Int.ofNat_nonneg _
    change 4 ≤ HeroLedger.energy value NetHack.Soko11Hero315.holeWeight soko1_1.initial final [186,212] outcomes
    omega

theorem pair_energy_universal {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (completed : Goal final) :
    4 ≤ Hero315Frame11.energy soko1_1.initial final [186,212] outcomes :=
  pair_energy LeftPair11.first_closed LeftPair11.closed logged completed
#print axioms pair_energy_universal
end Owner1007.LeftEnergy11
