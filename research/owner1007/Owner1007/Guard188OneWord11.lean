import Owner1007.Guard188One11
import Owner1007.Guard188Word11
import Owner1007.Guard188Strict11
import Owner1007.CutStrict11
namespace Owner1007.Guard188OneWord11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.Guard188Word11

theorem actor_bound {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (checked : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
    (unique : group.Nodup) (inside : group⊆state.boulders)
    (pays : OwnedCorral11.PaidStep Guard188One11.actorPaid group dir t) :
    2≤charge NetHack.Soko11Hero315.holeWeight group outcome + value t.state (update group outcome) - value state group := by
  obtain ⟨source,owner,metadata,paid⟩ := pays
  rcases paid with old|new
  · exact Guard188Strict11.exit_row scalar rfl valid checked effect unique inside ⟨source,owner,metadata,old⟩
  · have cut : CutActor11.Exit source dir := by rcases new with ⟨rfl,rfl⟩; simp [CutActor11.Exit]
    exact CutStrict11.exit_row scalar rfl valid checked effect unique inside ⟨source,owner,metadata,cut⟩

theorem one_step
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Guard188One11.locks Guard188One11.region Guard188One11.paid)
    {state : State} {dir : Dir} {t : Transition} {outcome : Outcome}
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (checked : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
    (fixed139 : 139∈state.boulders)
    (i : Fin 6) (present : Guard188One11.cell i∈state.boulders) (heroInside : state.player∈Guard188One11.region i)
    (zero139 : ownPush [139] outcome=0)
    (cheap : charge NetHack.Soko11Hero315.holeWeight [Guard188One11.cell i] outcome +
      value t.state (update [Guard188One11.cell i] outcome) - value state [Guard188One11.cell i]<2) :
    ∃ j : Fin 6, t.state.player∈Guard188One11.region j ∧ update [Guard188One11.cell i] outcome=[Guard188One11.cell j] := by
  have inside : Guard188One11.locks i⊆state.boulders := by
    intro cell found
    simp [Guard188One11.locks] at found
    rcases found with rfl|rfl
    · exact fixed139
    · exact present
  have good : OwnedCorral11.Good Guard188One11.locks Guard188One11.region state (Guard188One11.locks i) :=
    ⟨i,heroInside,List.Subset.refl _⟩
  have avoid : ¬ OwnedCorral11.PaidStep Guard188One11.paid (Guard188One11.locks i) dir t := by
    rintro ⟨source,owner,metadata,paid⟩
    rcases paid with gate139|actorPaid
    · exact zero_source 139 effect zero139 (gate139 ▸ metadata)
    · have not139 : source≠139 := by
        rcases actorPaid with old|⟨rfl,_⟩
        · rcases old with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> decide
        · decide
      have ownerParts : source=139 ∨ source=Guard188One11.cell i := by simpa [Guard188One11.locks] using owner
      have same : source=Guard188One11.cell i := ownerParts.resolve_left not139
      have actorOwner : source∈[Guard188One11.cell i] := by simpa only [List.mem_singleton] using same
      have bound := actor_bound valid checked effect (by simp)
        (show [Guard188One11.cell i]⊆state.boulders by simpa using present) ⟨source,actorOwner,metadata,actorPaid⟩
      omega
  have holesInside : state.holes⊆soko1_1.initial.holes := by
    obtain ⟨phase,atIndex⟩ := valid.2
    rw [atIndex.2.1]
    exact (List.drop_sublist phase _).subset
  have bounded : (Guard188One11.locks i).length≤2 := by rw [Guard188One11.size]; omega
  obtain ⟨j,nextHero,nextLocks⟩ := OwnedCorral11.step_good_except closed Guard188One11.unique Guard188One11.size
    good inside bounded holesInside checked effect avoid
  have permutation := GhostSubset.pair_update_perm [139] [Guard188One11.cell i] (Guard188One11.unique i) outcome
  rw [ownPush_zero_update [139] outcome zero139] at permutation
  have member : Guard188One11.cell j∈[139]++update [Guard188One11.cell i] outcome :=
    permutation.mem_iff.mpr (nextLocks (by simp [Guard188One11.locks]))
  have selected : Guard188One11.cell j∈update [Guard188One11.cell i] outcome := by
    rcases List.mem_append.mp member with fixed|selected
    · have same : Guard188One11.cell j=139 := by simpa using fixed
      exact False.elim (Guard188One11.not_fixed j same)
    · exact selected
  have nextBound : (update [Guard188One11.cell i] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
  exact ⟨j,nextHero,singleton_of_member _ _ nextBound selected⟩

theorem guard_logged
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Guard188One11.locks Guard188One11.region Guard188One11.paid)
    {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (fixed139 : 139∈state.boulders)
    (i : Fin 6) (present : Guard188One11.cell i∈state.boulders) (heroInside : state.player∈Guard188One11.region i)
    (stationary139 : ownPushes [139] outcomes=0)
    (cheap : energy state final [Guard188One11.cell i] outcomes<2) :
    ∃ j : Fin 6, final.player∈Guard188One11.region j ∧ endGroup [Guard188One11.cell i] outcomes=[Guard188One11.cell j] := by
  induction logged generalizing i with
  | nil => exact ⟨i,heroInside,rfl⟩
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    let cert := groupCertificate 1
    have nextValid := cert.preserved state dir t valid head
    have nextActual := step_boulders_nodup _ _ _ _ valid.1 head
    have zero139 : ownPush [139] outcome=0 := by simp only [ownPushes] at stationary139; omega
    have same139 := ownPush_zero_update [139] outcome zero139
    have tail139 : ownPushes [139] outcomes=0 := by simpa only [ownPushes,zero139,same139,Nat.zero_add] using stationary139
    have next139 := fixed_next 139 effect fixed139 zero139
    have inside : [Guard188One11.cell i]⊆state.boulders := by simpa using present
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual [Guard188One11.cell i] (by simp) inside
    have nextSubset := GhostSubset.update_subset state t outcome effect [Guard188One11.cell i] (by simp) inside
    have nextSize : (update [Guard188One11.cell i] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
    have nonnegative := HeroLedger.Logged.energy_nonnegative tail cert nextValid
      (update [Guard188One11.cell i] outcome) nextUnique nextSubset nextSize
    have one := cert.row state dir t outcome [Guard188One11.cell i] valid (by simp) inside (by simp) head effect
    change value state [Guard188One11.cell i]≤charge NetHack.Soko11Hero315.holeWeight [Guard188One11.cell i] outcome +
      value t.state (update [Guard188One11.cell i] outcome) at one
    have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight
      state t.state final [Guard188One11.cell i] outcome outcomes
    change energy state final [Guard188One11.cell i] (outcome::outcomes) =
      charge NetHack.Soko11Hero315.holeWeight [Guard188One11.cell i] outcome +
      value t.state (update [Guard188One11.cell i] outcome) - value state [Guard188One11.cell i] +
      energy t.state final (update [Guard188One11.cell i] outcome) outcomes at decomposition
    change 0≤energy t.state final (update [Guard188One11.cell i] outcome) outcomes at nonnegative
    have firstCheap : charge NetHack.Soko11Hero315.holeWeight [Guard188One11.cell i] outcome +
      value t.state (update [Guard188One11.cell i] outcome) - value state [Guard188One11.cell i]<2 := by omega
    obtain ⟨j,nextHero,updated⟩ := one_step closed valid head effect fixed139 i present heroInside zero139 firstCheap
    have nextPresent : Guard188One11.cell j∈t.state.boulders := nextSubset (by rw [updated]; simp)
    have tailCheap : energy t.state final [Guard188One11.cell j] outcomes<2 := by rw [←updated]; omega
    obtain ⟨last,lastHero,lastGroup⟩ := ih nextValid next139 j nextPresent nextHero tail139 tailCheap
    exact ⟨last,lastHero,by simpa only [endGroup,updated] using lastGroup⟩

theorem guard188
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Guard188One11.locks Guard188One11.region Guard188One11.paid)
    {dirs state pushes moves outcomes}
    (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
    (stationary139 : ownPushes [139] outcomes=0)
    (cheap : energy soko1_1.initial state [188] outcomes<2) :
    ∃ i : Fin 6, state.player∈Guard188One11.region i ∧ endGroup [188] outcomes=[Guard188One11.cell i] :=
  guard_logged closed first NetHack.SokobanLinearPhases.Map11.initial_good (by decide)
    ⟨0,by decide⟩ (by decide) (by decide) stationary139 cheap

#print axioms guard188
end Owner1007.Guard188OneWord11
