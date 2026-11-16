import Owner1007.AfterJ12
import Owner1007.NorthBound12
namespace Owner1007.AfterJBound12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
open Owner1007.AfterJ12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
abbrev p := Generated.soko1_2Potential

theorem matrices (kind : Fin 2) : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes
    (locks kind) (region kind) (paid kind) = true := by
  obtain ⟨k,bound⟩ := kind
  have choices : k=0 ∨ k=1 := by omega
  rcases choices with rfl | rfl
  · exact matrix210
  · exact matrix238

theorem ordinary_paid_sources (source : Cell) (dir : Dir) (paid : ordinaryPaid source dir) :
    source∈([210,236,237,238,264,265,318,291] : List Cell) := by
  rcases paid with ⟨h,_⟩ | ⟨rfl,_⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · decide +kernel
theorem ordinary_not318 : ∀ kind, 318∉ordinary kind := by decide +kernel
theorem priced_min {kind source dir} (pays : paid kind source dir) :
    ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧
      (if source=318 then (3:Int) else 2) ≤ 1+p.boulder dest-p.boulder source := by
  intro dest member
  have sourceInside : source∈([210,236,237,238,264,265,318,291] : List Cell) := by
    rcases pays with ⟨member,paid⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact ordinary_paid_sources source dir paid
    · decide +kernel
    · decide +kernel
  exact paid_cost kind source sourceInside dir (Geometry.all_directions dir) pays dest member

theorem ring_priced (kind : Fin 2) : ∀ source dir, ringPaid kind source dir →
    ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest∉soko1_2.initial.holes ∧ (2:Int)≤1+p.boulder dest-p.boulder source := by
  intro source dir pays dest member
  have sourceInside : source∈([236,210,237,263,290] : List Cell) := by
    rcases pays with h | h | h | h | h <;> simp_all
  have bound := ringCost kind source sourceInside dir (Geometry.all_directions dir) pays dest member
  exact ⟨bound.1,by rw [bound.2]; exact Int.le_refl _⟩

theorem cash_cases {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (completed : Goal final) (kind : Fin 2)
    (group : List Cell) (gUnique : group.Nodup) (gSubset : group ⊆ state.boulders)
    (i : Fin 5) (hero : state.player ∈ region kind i) (inside : locks kind i ⊆ group) :
    2≤energy p (ordinary kind) outcomes ∨ 4≤energy p group outcomes ∨
      (3≤energy p group outcomes ∧ endGroup [318] outcomes≠[]) := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ (matrices kind)
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed (unique kind) logged reached group gUnique gSubset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroOne,locksOne,pays,unchanged⟩ :=
      event.split_fixed (fixed kind) (fixed_inside kind) (fixed_guard kind) reached gUnique gSubset
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldInside := first.end_subset actualUnique group gUnique gSubset
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
      (endGroup group before) oldInside.1 oldInside.2
    have nextSubset := GhostSubset.update_subset middle t outcome effect
      (endGroup group before) oldInside.1 oldInside.2
    have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
    cases outcome with
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,paid⟩ := pays
      have rawCost := push_effect_price p soko1_2.initial.holes (if source=318 then (3:Int) else 2)
        middleReached.holes_sublist.subset (priced_min paid) checked effect
      have allBound := event_energy_le Generated.soko1_2_potential_valid group first last (.push source ending)
      simp only [projectedOutcome,if_pos owner] at allBound
      change slack p (.push source ending) ≤ energy p group (before ++ .push source ending :: after) at allBound
      rcases paid with h | h | h
      · obtain ⟨member,direction⟩ := h
        have prior := unchanged (ordinary kind) (fun _ h => List.mem_append_left _ h)
        have bound := event_energy_le Generated.soko1_2_potential_valid (ordinary kind) first last (.push source ending)
        simp only [prior,projectedOutcome,if_pos member] at bound
        change slack p (.push source ending) ≤ energy p (ordinary kind) (before ++ .push source ending :: after) at bound
        have different : source≠318 := by intro same; exact ordinary_not318 kind (same ▸ member)
        have two : (2:Int)≤slack p (.push source ending) := by simpa only [if_neg different] using rawCost
        exact Or.inl (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
          (by decide +kernel) checked effect
        subst ending
        have prior := unchanged [318] (by intro c h; have same:=List.mem_singleton.mp h; subst c; exact List.mem_append_right _ (by simp))
        have shapeNext : t.state.boulders=317::middle.boulders.erase 318 := by
          simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
        have present : 317∈t.state.boulders := by rw [shapeNext]; simp
        have survives := NorthBound12.after_park_survives last nextActual 318 317 present
          NorthBound12.locked317 before prior
        have three : (3:Int)≤slack p (.push 318 (.stay 317)) := by simpa using rawCost
        exact Or.inr (Or.inr ⟨by rw [shape]; omega,by rw [shape]; exact survives⟩)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          NorthEvents12.ring_activation (by decide +kernel) checked effect
        subst ending
        have erased := GhostSubset.erase_subset locksOne (unique kind j) 291
        have ringInside : ringLocks kind 0 ⊆ update (endGroup group before) (.push 291 (.stay 290)) := by
          simp only [update,move,if_pos owner,post]
          exact List.Subset.trans (ringActivation kind j) (List.cons_subset_cons 290 erased)
        have heroNext : t.state.player=291 := matches_hero middle t (.push 291 (.stay 290)) effect
        have ringHeroNext : t.state.player∈ringRegion kind 0 := by rw [heroNext]; exact ringHero kind
        have ringClosed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ (ringMatrix kind)
        have later := closedExcept_energy ringClosed (ringUnique kind) (ringLarge kind) 2 (ring_priced kind)
          last nextReached (update (endGroup group before) (.push 291 (.stay 290)))
          nextUnique nextSubset completed ringHeroNext ringInside
        change 2≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after at later
        have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
        change 0≤ownSlack p group before at prefixNN
        have two : (2:Int)≤slack p (.push 291 (.stay 290)) := by simpa using rawCost
        exact Or.inr (Or.inl (by rw [shape,energy_at_split]; simp only [projectedOutcome,if_pos owner]; omega))
  · obtain ⟨j,hero,locksInside⟩ := terminal
    have endInside := logged.end_subset actualUnique group gUnique gSubset
    have count := List.Nodup.length_le_of_subset (unique kind j) (List.Subset.trans locksInside endInside.2)
    have large := size kind j
    have conserved := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    change 20+final.holes.length=final.boulders.length+18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega

def startSource (kind : Fin 2) : Cell := if kind.val=0 then 210 else 238
def startDest (kind : Fin 2) : Cell := if kind.val=0 then 236 else 264
def headOutcome (kind : Fin 2) : Outcome := .push (startSource kind) (.stay (startDest kind))
theorem activation : ∀ kind i, locks kind i ⊆ startDest kind :: (NorthEvents12.locks i).erase (startSource kind) := by decide +kernel
theorem source_inside : ∀ kind i, startSource kind ∈ NorthEvents12.locks i := by decide +kernel
theorem source_J : ∀ kind, startSource kind∈NorthBound12.J := by decide +kernel
theorem source_not318 : ∀ kind, startSource kind∉[318] := by decide +kernel
theorem first_price : ∀ kind, slack p (headOutcome kind)=2 := by decide +kernel
theorem ordinary_after : ∀ kind, (update NorthBound12.J (headOutcome kind)).Perm (ordinary kind) := by decide +kernel

theorem firstJ_cases {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final) (kind : Fin 2)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ headOutcome kind :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .south=some t)
    (effect : Matches middle t (headOutcome kind))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before)
    (unchanged : ∀ small : List Cell, small ⊆ NorthEvents12.J → endGroup small before=small) :
    6≤energy p NorthBound12.G outcomes ∨
      (5≤energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes≠[]) := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have oldInside := first.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have nextUnique := GhostSubset.update_unique middle t (headOutcome kind) effect nextActual
    (endGroup NorthBound12.G before) oldInside.1 oldInside.2
  have nextSubset := GhostSubset.update_subset middle t (headOutcome kind) effect
    (endGroup NorthBound12.G before) oldInside.1 oldInside.2
  have owner : startSource kind ∈ endGroup NorthBound12.G before := locksInside (source_inside kind i)
  have erased := GhostSubset.erase_subset locksInside (NorthEvents12.unique i) (startSource kind)
  have nextLocks : locks kind i ⊆ update (endGroup NorthBound12.G before) (headOutcome kind) := by
    simp only [headOutcome,update,move,if_pos owner,post]
    exact List.Subset.trans (activation kind i) (List.cons_subset_cons (startDest kind) erased)
  have heroNext : t.state.player=startSource kind :=
    matches_hero middle t (headOutcome kind) effect
  have nextHero : t.state.player∈region kind i := by
    rw [heroNext]
    change startSource kind∈NorthEvents12.region i ++ [startSource kind]
    exact List.mem_append_right _ (by simp)
  have later := cash_cases last nextReached completed kind
    (update (endGroup NorthBound12.G before) (headOutcome kind)) nextUnique nextSubset i nextHero nextLocks
  have priorJ := unchanged NorthBound12.J (by decide +kernel)
  have prior318 := unchanged [318] (by decide +kernel)
  have wholeJ : energy p NorthBound12.J outcomes =
      ownSlack p NorthBound12.J before + 2 + energy p (ordinary kind) after := by
    rw [shape,energy_at_split,priorJ]
    have member := source_J kind
    simp only [headOutcome,projectedOutcome,if_pos member]
    change ownSlack p NorthBound12.J before + slack p (headOutcome kind) +
      energy p (update NorthBound12.J (headOutcome kind)) after =
      ownSlack p NorthBound12.J before + 2 + energy p (ordinary kind) after
    rw [first_price,energy_perm p (ordinary_after kind) after]
  have wholeG : energy p NorthBound12.G outcomes =
      ownSlack p NorthBound12.G before + 2 +
        energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after := by
    rw [shape,energy_at_split]
    simp only [headOutcome,projectedOutcome,if_pos owner]
    change ownSlack p NorthBound12.G before + slack p (headOutcome kind) +
      energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after =
      ownSlack p NorthBound12.G before + 2 +
      energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after
    rw [first_price]
  have nnJ := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.J
  have nnG := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.G
  change 0≤ownSlack p NorthBound12.J before at nnJ
  change 0≤ownSlack p NorthBound12.G before at nnG
  have bottom := NorthBound12.bottom_north_energy_two logged
  change 2≤energy p NorthBound12.BottomN outcomes at bottom
  have gSplit := logged.energy_split initialUnique p NorthBound12.J NorthBound12.BottomN
    (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.G outcomes =
    energy p NorthBound12.J outcomes + energy p NorthBound12.BottomN outcomes at gSplit
  rcases later with ordinaryTwo | four | ⟨three,survives⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega,?_⟩
    rw [shape,endGroup_append,prior318]
    simpa only [endGroup,headOutcome,update,move,if_neg (source_not318 kind)] using survives

#print axioms cash_cases
#print axioms firstJ_cases
end Owner1007.AfterJBound12

