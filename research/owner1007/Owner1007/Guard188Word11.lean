import Owner1007.Guard18811
import Owner1007.Guard188Strict11
import Owner1007.Hero315Frame11
import Owner1007.OwnedCorral11
import Owner1007.TokenPersistence
namespace Owner1007.Guard188Word11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem zero_source {state : State} {t : Transition} {outcome : Outcome} (fixed : Cell)
    (effect : Matches state t outcome) (zero : ownPush [fixed] outcome=0) : t.pushSource≠some fixed := by
  cases outcome with
  | walk target => rw [effect]; simp
  | push source result =>
    have different : source≠fixed := by intro same; subst source; simp [ownPush] at zero
    cases result with
    | stay landing => rw [effect.2]; intro same; exact different (Option.some.inj same)
    | fill hole => rw [effect.2.2]; intro same; exact different (Option.some.inj same)

theorem fixed_update (outcome : Outcome)
    (zero137 : ownPush [137] outcome=0) (zero139 : ownPush [139] outcome=0) :
    update [137,139] outcome=[137,139] := by
  cases outcome with
  | walk target => rfl
  | push source result =>
    have not137 : source≠137 := by intro same; subst source; simp [ownPush] at zero137
    have not139 : source≠139 := by intro same; subst source; simp [ownPush] at zero139
    simp [update,move,not137,not139]

theorem singleton_of_member (cells : List Cell) (cell : Cell) (bounded : cells.length≤1)
    (member : cell∈cells) : cells=[cell] := by
  cases cells with
  | nil => contradiction
  | cons first rest =>
    cases rest with
    | nil =>
      have same : cell=first := by simpa only [List.mem_singleton] using member
      exact congrArg (fun c => [c]) same.symm
    | cons next rest => simp only [List.length_cons] at bounded; omega

theorem one_step
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Guard18811.locks Guard18811.region Guard18811.paid)
    {state : State} {dir : Dir} {t : Transition} {outcome : Outcome}
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (checked : step soko1_1.board state dir = some t) (effect : Matches state t outcome)
    (fixed137 : 137∈state.boulders) (fixed139 : 139∈state.boulders)
    (i : Fin 6) (present : Guard18811.cell i∈state.boulders) (heroInside : state.player∈Guard18811.region i)
    (zero137 : ownPush [137] outcome=0) (zero139 : ownPush [139] outcome=0)
    (cheap : charge NetHack.Soko11Hero315.holeWeight [Guard18811.cell i] outcome +
      value t.state (update [Guard18811.cell i] outcome) - value state [Guard18811.cell i]<2) :
    ∃ j : Fin 6, t.state.player∈Guard18811.region j ∧ update [Guard18811.cell i] outcome=[Guard18811.cell j] := by
  have inside : Guard18811.locks i ⊆ state.boulders := by
    intro cell found
    simp [Guard18811.locks] at found
    rcases found with rfl|rfl|rfl
    · exact fixed137
    · exact fixed139
    · exact present
  have good : OwnedCorral11.Good Guard18811.locks Guard18811.region state (Guard18811.locks i) :=
    ⟨i,heroInside,List.Subset.refl _⟩
  have avoid : ¬ OwnedCorral11.PaidStep Guard18811.paid (Guard18811.locks i) dir t := by
    rintro ⟨source,owner,metadata,paid⟩
    rcases paid with gate137 | gate139 | actorPaid
    · exact zero_source 137 effect zero137 (gate137 ▸ metadata)
    · exact zero_source 139 effect zero139 (gate139 ▸ metadata)
    · have not137 : source≠137 := by
        rcases actorPaid with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> decide
      have not139 : source≠139 := by
        rcases actorPaid with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> decide
      have ownerParts : source=137 ∨ source=139 ∨ source=Guard18811.cell i := by simpa [Guard18811.locks] using owner
      have same : source=Guard18811.cell i := ownerParts.resolve_left not137 |>.resolve_left not139
      have actorOwner : source∈[Guard18811.cell i] := by simpa only [List.mem_singleton] using same
      have actorBound := Guard188Strict11.exit_row scalar rfl valid checked effect (by simp)
        (show [Guard18811.cell i] ⊆ state.boulders by simpa using present) ⟨source,actorOwner,metadata,actorPaid⟩
      change 2≤charge NetHack.Soko11Hero315.holeWeight [Guard18811.cell i] outcome +
        value t.state (update [Guard18811.cell i] outcome) - value state [Guard18811.cell i] at actorBound
      omega
  have holesInside : state.holes⊆soko1_1.initial.holes := by
    obtain ⟨phase,atIndex⟩ := valid.2
    rw [atIndex.2.1]
    exact (List.drop_sublist phase _).subset
  have bounded : (Guard18811.locks i).length≤3 := by rw [Guard18811.size]; omega
  obtain ⟨j,nextHero,nextLocks⟩ := OwnedCorral11.step_good_except closed Guard18811.unique Guard18811.size
    good inside bounded holesInside checked effect avoid
  have permutation := GhostSubset.pair_update_perm [137,139] [Guard18811.cell i] (Guard18811.unique i) outcome
  rw [fixed_update outcome zero137 zero139] at permutation
  have member : Guard18811.cell j∈[137,139] ++ update [Guard18811.cell i] outcome :=
    permutation.mem_iff.mpr (nextLocks (by simp [Guard18811.locks]))
  have selected : Guard18811.cell j∈update [Guard18811.cell i] outcome := by
    rcases List.mem_append.mp member with fixed | selected
    · have two : Guard18811.cell j=137 ∨ Guard18811.cell j=139 := by simpa using fixed
      exact False.elim (two.elim (Guard18811.not_fixed j).1 (Guard18811.not_fixed j).2)
    · exact selected
  have nextBound : (update [Guard18811.cell i] outcome).length≤1 :=
    Nat.le_trans (update_length _ _) (by simp)
  exact ⟨j,nextHero,singleton_of_member _ _ nextBound selected⟩

#print axioms one_step
end Owner1007.Guard188Word11

namespace Owner1007.Guard188Word11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem fixed_next {state : State} {t : Transition} {outcome : Outcome} (fixed : Cell)
    (effect : Matches state t outcome) (present : fixed∈state.boulders) (zero : ownPush [fixed] outcome=0) :
    fixed∈t.state.boulders := by
  have inside : [fixed] ⊆ state.boulders := by simpa using present
  have next := GhostSubset.update_subset state t outcome effect [fixed] (by simp) inside
  rw [ownPush_zero_update [fixed] outcome zero] at next
  exact next (by simp)

theorem guard_logged
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Guard18811.locks Guard18811.region Guard18811.paid)
    {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
    (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
    (fixed137 : 137∈state.boulders) (fixed139 : 139∈state.boulders)
    (i : Fin 6) (present : Guard18811.cell i∈state.boulders) (heroInside : state.player∈Guard18811.region i)
    (stationary137 : ownPushes [137] outcomes=0) (stationary139 : ownPushes [139] outcomes=0)
    (cheap : energy state final [Guard18811.cell i] outcomes<2) :
    ∃ j : Fin 6, final.player∈Guard18811.region j ∧ endGroup [Guard18811.cell i] outcomes=[Guard18811.cell j] := by
  induction logged generalizing i with
  | nil => exact ⟨i,heroInside,rfl⟩
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    let cert := groupCertificate 1
    have nextValid := cert.preserved state dir t valid head
    have nextActual := step_boulders_nodup _ _ _ _ valid.1 head
    have zero137 : ownPush [137] outcome=0 := by simp only [ownPushes] at stationary137; omega
    have zero139 : ownPush [139] outcome=0 := by simp only [ownPushes] at stationary139; omega
    have same137 := ownPush_zero_update [137] outcome zero137
    have same139 := ownPush_zero_update [139] outcome zero139
    have tail137 : ownPushes [137] outcomes=0 := by
      simpa only [ownPushes,zero137,same137,Nat.zero_add] using stationary137
    have tail139 : ownPushes [139] outcomes=0 := by
      simpa only [ownPushes,zero139,same139,Nat.zero_add] using stationary139
    have next137 := fixed_next 137 effect fixed137 zero137
    have next139 := fixed_next 139 effect fixed139 zero139
    have inside : [Guard18811.cell i] ⊆ state.boulders := by simpa using present
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual [Guard18811.cell i] (by simp) inside
    have nextSubset := GhostSubset.update_subset state t outcome effect [Guard18811.cell i] (by simp) inside
    have nextSize : (update [Guard18811.cell i] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
    have nonnegative := HeroLedger.Logged.energy_nonnegative tail cert nextValid
      (update [Guard18811.cell i] outcome) nextUnique nextSubset nextSize
    have one := cert.row state dir t outcome [Guard18811.cell i] valid (by simp) inside (by simp) head effect
    change value state [Guard18811.cell i] ≤ charge NetHack.Soko11Hero315.holeWeight [Guard18811.cell i] outcome +
      value t.state (update [Guard18811.cell i] outcome) at one
    have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight
      state t.state final [Guard18811.cell i] outcome outcomes
    change energy state final [Guard18811.cell i] (outcome :: outcomes) =
      charge NetHack.Soko11Hero315.holeWeight [Guard18811.cell i] outcome +
      value t.state (update [Guard18811.cell i] outcome) - value state [Guard18811.cell i] +
      energy t.state final (update [Guard18811.cell i] outcome) outcomes at decomposition
    change 0≤energy t.state final (update [Guard18811.cell i] outcome) outcomes at nonnegative
    have firstCheap : charge NetHack.Soko11Hero315.holeWeight [Guard18811.cell i] outcome +
      value t.state (update [Guard18811.cell i] outcome) - value state [Guard18811.cell i]<2 := by omega
    obtain ⟨j,nextHero,updated⟩ := one_step closed valid head effect fixed137 fixed139 i present heroInside zero137 zero139 firstCheap
    have nextPresent : Guard18811.cell j∈t.state.boulders := nextSubset (by rw [updated]; simp)
    have tailCheap : energy t.state final [Guard18811.cell j] outcomes<2 := by rw [←updated]; omega
    obtain ⟨last,lastHero,lastGroup⟩ := ih nextValid next137 next139 j nextPresent nextHero tail137 tail139 tailCheap
    exact ⟨last,lastHero,by simpa only [endGroup,updated] using lastGroup⟩

theorem guard188
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Guard18811.locks Guard18811.region Guard18811.paid)
    {dirs state pushes moves outcomes}
    (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
    (stationary137 : ownPushes [137] outcomes=0) (stationary139 : ownPushes [139] outcomes=0)
    (cheap : energy soko1_1.initial state [188] outcomes<2) :
    ∃ i : Fin 6, state.player∈Guard18811.region i ∧ endGroup [188] outcomes=[Guard18811.cell i] :=
  guard_logged closed first NetHack.SokobanLinearPhases.Map11.initial_good
    (by decide) (by decide) ⟨0,by decide⟩ (by decide) (by decide) stationary137 stationary139 cheap

#print axioms guard188
end Owner1007.Guard188Word11
