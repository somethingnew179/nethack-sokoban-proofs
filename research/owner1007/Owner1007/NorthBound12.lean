import Owner1007.OwnedEventsMore12
import Owner1007.NorthEvents12
import Owner1007.RingCut12
import Owner1007.LockedTokens
import Owner1007.BottomEnergy12
namespace Owner1007.NorthBound12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def J : List Cell := [210,237,238,263,265]
def G : List Cell := [210,237,238,263,265,318,345]
def northWalk : Transition := {state := {soko1_2.initial with player := 397},pushed := false,filled := none}
def northPush : Transition := {state := FirstSplit12.afterN,pushed := true,filled := none,pushSource := some 371,landing := some 345}
theorem north_reached : Trace soko1_2.board soko1_2.initial [.east,.north] FirstSplit12.afterN 1 2 := by
  exact Trace.cons (next:=northWalk) (by decide +kernel)
    (Trace.cons (next:=northPush) (by decide +kernel) (Trace.nil _))
theorem locked317 : Locked soko1_2.board [317] := locked_of_check _ _ (by decide +kernel)
theorem locked_singleton_survives {board state dirs final pushes moves outcomes}
    (logged : Logged board state dirs final pushes moves outcomes)
    (unique : state.boulders.Nodup) (park : Cell) (present : park ∈ state.boulders)
    (locked : Locked board [park]) : endGroup [park] outcomes ≠ [] := by
  have kept := logged.locked_end_inside unique [park] (by simp)
    (by intro c h; have same : c=park := List.mem_singleton.mp h; simpa only [same] using present)
    [park] locked (fun _ h => h)
  intro empty
  have member := kept (List.mem_cons_self)
  simp only [empty,List.not_mem_nil] at member
theorem after_park_survives {board state dirs final pushes moves outcomes}
    (logged : Logged board state dirs final pushes moves outcomes)
    (unique : state.boulders.Nodup) (source park : Cell)
    (present : park ∈ state.boulders) (locked : Locked board [park])
    (before : List Outcome) (prior : endGroup [source] before = [source]) :
    endGroup [source] (before ++ .push source (.stay park) :: outcomes) ≠ [] := by
  rw [endGroup_append,prior]
  simpa only [endGroup,update,move,List.mem_cons,List.not_mem_nil,or_false,if_true,
    post,List.erase_cons_head] using locked_singleton_survives logged unique park present locked

theorem ring_priced : ∀ source dir, RingCut12.paid source dir →
    ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧
      (2 : Int) ≤ 1 + p.boulder dest - p.boulder source := by
  intro source dir paid dest member
  have sourceInside : source ∈ ([210,237,263,290] : List Cell) := by
    rcases paid with h | h | h | h <;> simp_all
  have bound := RingCut12.paid_cost source sourceInside dir (Geometry.all_directions dir) paid dest member
  exact ⟨bound.1,by rw [bound.2]; exact Int.le_refl _⟩
theorem north_priced {source dir} (paid : NorthEvents12.paid source dir) :
    ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧
      (if source=318 then (3 : Int) else 2) ≤ 1 + p.boulder dest - p.boulder source := by
  intro dest member
  have sourceInside : source ∈ ([210,238,265,318,291] : List Cell) := by
    rcases paid with h | h | h | h | h <;> simp_all
  have bound := NorthEvents12.paid_cost source sourceInside dir (Geometry.all_directions dir) paid dest member
  exact ⟨bound.1,by rw [bound.2]; exact Int.le_refl _⟩
theorem ring_activation (i : Fin 5) :
    RingCut12.locks 0 ⊆ 290 :: (NorthEvents12.locks i).erase 291 := by
  have all : ∀ i : Fin 5, RingCut12.locks 0 ⊆ 290 :: (NorthEvents12.locks i).erase 291 := by decide +kernel
  exact all i

theorem numeric_cases {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final) :
    2 ≤ energy p J outcomes ∨ 4 ≤ energy p G outcomes ∨
      (3 ≤ energy p G outcomes ∧ endGroup [318] outcomes ≠ []) := by
  have nClosed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ NorthEvents12.matrix
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have gUnique : G.Nodup := by decide +kernel
  have gSubset : G ⊆ FirstSplit12.afterN.boulders := by decide +kernel
  rcases event_or_good nClosed NorthEvents12.unique logged north_reached G gUnique gSubset
    (i:=0) (by decide +kernel) (by decide +kernel) with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,hero,locks,pays,fixed⟩ :=
      event.split_fixed NorthEvents12.J NorthEvents12.j_inside NorthEvents12.j_guard
        north_reached gUnique gSubset
    have middleReached := north_reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldGhost := first.end_subset initialUnique G gUnique gSubset
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    have nextGhostUnique := GhostSubset.update_unique middle t outcome effect nextActual
      (endGroup G before) oldGhost.1 oldGhost.2
    have nextGhostSubset := GhostSubset.update_subset middle t outcome effect
      (endGroup G before) oldGhost.1 oldGhost.2
    have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
    cases outcome with
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,paid⟩ := pays
      have rawCost := push_effect_price p soko1_2.initial.holes (if source=318 then (3 : Int) else 2)
        middleReached.holes_sublist.subset (north_priced paid) checked effect
      have allBound := event_energy_le Generated.soko1_2_potential_valid G first last (.push source ending)
      simp only [projectedOutcome,if_pos owner] at allBound
      dsimp only [p] at *
      rcases paid with h | h | h | h | h
      · obtain ⟨rfl,rfl⟩ := h
        have prior := fixed J (by decide +kernel)
        have bound := event_energy_le Generated.soko1_2_potential_valid J first last (.push 210 ending)
        simp only [prior,projectedOutcome] at bound
        have member : (210 : Cell) ∈ J := by decide +kernel
        simp only [if_pos member] at bound
        have two : (2 : Int) ≤ slack p (.push 210 ending) := by simpa using rawCost
        exact Or.inl (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have prior := fixed J (by decide +kernel)
        have bound := event_energy_le Generated.soko1_2_potential_valid J first last (.push 238 ending)
        simp only [prior,projectedOutcome] at bound
        have member : (238 : Cell) ∈ J := by decide +kernel
        simp only [if_pos member] at bound
        have two : (2 : Int) ≤ slack p (.push 238 ending) := by simpa using rawCost
        exact Or.inl (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have prior := fixed J (by decide +kernel)
        have bound := event_energy_le Generated.soko1_2_potential_valid J first last (.push 265 ending)
        simp only [prior,projectedOutcome] at bound
        have member : (265 : Cell) ∈ J := by decide +kernel
        simp only [if_pos member] at bound
        have two : (2 : Int) ≤ slack p (.push 265 ending) := by simpa using rawCost
        exact Or.inl (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 318 .west = [317] by decide +kernel)
          (by decide +kernel) checked effect
        subst ending
        have shapeNext : t.state.boulders = 317 :: middle.boulders.erase 318 := by
          simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
        have present : (317 : Cell) ∈ t.state.boulders := by rw [shapeNext]; simp
        have prior := fixed [318] (by decide +kernel)
        have survives := after_park_survives last nextActual 318 317 present locked317 before prior
        exact Or.inr (Or.inr ⟨by rw [shape]; simpa using Int.le_trans rawCost allBound,
          by rw [shape]; exact survives⟩)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          NorthEvents12.ring_activation (by decide +kernel) checked effect
        subst ending
        have erased := GhostSubset.erase_subset locks (NorthEvents12.unique i) 291
        have ringInside : RingCut12.locks 0 ⊆ update (endGroup G before) (.push 291 (.stay 290)) := by
          simp only [update,move,if_pos owner,post]
          exact List.Subset.trans (ring_activation i) (List.cons_subset_cons 290 erased)
        have heroNext : t.state.player = 291 := matches_hero middle t (.push 291 (.stay 290)) effect
        have ringHero : t.state.player ∈ RingCut12.region 0 := by rw [heroNext]; decide +kernel
        have ringClosed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ RingCut12.matrix
        have ringLarge : ∀ i, 2 < (RingCut12.locks i).length := by decide +kernel
        have later := closedExcept_energy ringClosed RingCut12.unique ringLarge 2 ring_priced
          last nextReached (update (endGroup G before) (.push 291 (.stay 290)))
          nextGhostUnique nextGhostSubset completed ringHero ringInside
        have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid G
        have two : (2 : Int) ≤ slack p (.push 291 (.stay 290)) := by simpa using rawCost
        exact Or.inr (Or.inl (by rw [shape,energy_at_split]; simp only [projectedOutcome,if_pos owner]; omega))
  · obtain ⟨i,hero,locks⟩ := terminal
    have inside := logged.end_subset initialUnique G gUnique gSubset
    have count := List.Nodup.length_le_of_subset (NorthEvents12.unique i) (List.Subset.trans locks inside.2)
    have large := NorthEvents12.size i
    have reachedFinal := north_reached.append logged.trace
    have conserved := reachedFinal.conservation
    have empty : final.holes=[] := completed
    change 20 + final.holes.length = final.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega

def BottomN : List Cell := [318,345]
theorem bottom_north_energy_two {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes) :
    2 ≤ energy p BottomN outcomes := by
  have closed := PricedCorral.closed_of_check _ _ _ _ _ _ BottomCut12.matrix
  obtain ⟨j,hero,inside,price⟩ := RightPrice4.owned_trace_price closed BottomCut12.unique
    logged north_reached BottomN (by decide +kernel) (by decide +kernel)
    (i:=1) (by decide +kernel) (by decide +kernel)
  have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -p.boulder c)
    (BottomCut12.locks j) (endGroup BottomN outcomes)
    (fun c => by have h := Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c ≤ 0 at h; omega)
    (BottomCut12.unique j) inside
  change Owner1007.debtOf p (BottomCut12.locks j) ≤ Owner1007.debtOf p (endGroup BottomN outcomes) at debt
  have credit := BottomCut12.debt_credit j
  change BottomCut12.credit j ≤ Owner1007.debtOf p (BottomCut12.locks j) at credit
  change 2 ≤ ownSlack p BottomN outcomes + BottomCut12.credit j at price
  unfold energy
  omega

theorem g_cases {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final) :
    4 ≤ energy p G outcomes ∨ (3 ≤ energy p G outcomes ∧ endGroup [318] outcomes ≠ []) := by
  rcases numeric_cases logged completed with ordinary | four | three
  · have bottom := bottom_north_energy_two logged
    have split := logged.energy_split (by decide +kernel) p J BottomN (by decide +kernel) (by decide +kernel)
    have shape : J ++ BottomN = G := rfl
    rw [shape] at split
    exact Or.inl (by omega)
  · exact Or.inl four
  · exact Or.inr three
#print axioms numeric_cases
#print axioms g_cases
end Owner1007.NorthBound12
