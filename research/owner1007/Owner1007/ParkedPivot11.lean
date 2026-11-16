import Owner1007.Upper187Cover11
import Owner1007.Parked18811
import Owner1007.ParkedStrict11
import Owner1007.WestRankHead11
namespace Owner1007.ParkedPivot11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def paid (source : Cell) (dir : Dir) : Prop := source=137 ∨ source=139 ∨ Parked18811.paid source dir
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Parked18811.locks Parked18811.region paid := by
 refine ⟨Parked18811.closed.1,?_⟩
 intro i hero heroInside dir source sourceInside adjacent
 rcases Parked18811.closed.2 i hero heroInside dir source sourceInside adjacent with blocked|pays|shift
 · exact Or.inl blocked
 · exact Or.inr (Or.inl (Or.inr (Or.inr pays)))
 · exact Or.inr (Or.inr shift)
def Shape (source : Cell) (dir : Dir) : Prop :=
 (source=137 ∧ dir=.west) ∨ (source=139 ∧ dir=.east) ∨
 (source=189 ∧ dir=.west) ∨ (source=190 ∧ (dir=.east ∨ dir=.west))
instance (source : Cell) (dir : Dir) : Decidable (Shape source dir) := by unfold Shape; infer_instance
def shapeCheck (i : Fin 9) : Bool := (Parked18811.locks i).all fun source => allDirs.all fun dir =>
 match advance soko1_1.board source dir.opposite with
 | none => true
 | some hero => decide (hero∈Parked18811.region i → ¬BlockedPush soko1_1.board (Parked18811.locks i) source dir →
     paid source dir → Shape source dir)
theorem shapes_checked : (List.finRange 9).all shapeCheck=true := by decide +kernel
theorem complete (i : Fin 9) (group : List Cell) (bound : group.length≤4)
 (inside : Parked18811.locks i⊆group) (source : Cell) (owner : source∈group) : source∈Parked18811.locks i := by
 by_cases member : source∈Parked18811.locks i
 · exact member
 · have all : source::Parked18811.locks i⊆group := by
     intro c found
     rcases List.mem_cons.mp found with rfl|later
     · exact owner
     · exact inside later
   have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,Parked18811.unique i⟩) all
   simp only [List.length_cons,Parked18811.size i] at card
   omega

theorem head_shape {state : State} {group : List Cell} {dir : Dir} {t : Transition}
 (good : OwnedCorral11.Good Parked18811.locks Parked18811.region state group)
 (inside : group⊆state.boulders) (bounded : group.length≤4)
 (head : step soko1_1.board state dir=some t) (pays : OwnedCorral11.PaidStep paid group dir t) :
 ∃source, source∈group ∧ t.pushSource=some source ∧ Shape source dir := by
 obtain ⟨i,heroInside,locksInside⟩ := good
 obtain ⟨source,owner,metadata,pays⟩ := pays
 have member := complete i group bounded locksInside source owner
 have unblocked := WestRankHead11.source_unblocked head metadata (List.Subset.trans locksInside inside)
 have adjacent := PairPost11.source_adjacent head metadata
 have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
   (step_player_clear _ _ _ _ head).1 dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp shapes_checked i (by simp)) source member) dir (Geometry.all_directions dir)
 simp only [reverse] at row
 exact ⟨source,owner,metadata,of_decide_eq_true row heroInside unblocked pays⟩

def Side (source : Cell) (dir : Dir) : Prop :=
 (source=189 ∧ dir=.west) ∨ (source=190 ∧ (dir=.east ∨ dir=.west))
instance (source : Cell) (dir : Dir) : Decidable (Side source dir) := by unfold Side; infer_instance
def CoverShift (i : Fin 9) (source : Cell) (dir : Dir) : Prop :=
 ∃j : Fin 36, ∃dest∈pushTargets soko1_1.board source dir,
 pushTargets soko1_1.board source dir=[dest] ∧ dest∉soko1_1.initial.holes ∧
 Upper187Cover11.locks j⊆dest::(Parked18811.locks i).erase source ∧ source∈Upper187Cover11.region j
instance (i : Fin 9) (source : Cell) (dir : Dir) : Decidable (CoverShift i source dir) := by unfold CoverShift; infer_instance
def transitionCheck (i : Fin 9) : Bool := (Parked18811.locks i).all fun source => allDirs.all fun dir =>
 match advance soko1_1.board source dir.opposite with
 | none => true
 | some hero => decide (hero∉Parked18811.region i ∨ BlockedPush soko1_1.board (Parked18811.locks i) source dir ∨
     ¬Side source dir ∨ CoverShift i source dir)
theorem transitions_checked : (List.finRange 9).all transitionCheck=true := by decide +kernel

theorem enter_cover {state : State} {group : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
 (good : OwnedCorral11.Good Parked18811.locks Parked18811.region state group)
 (inside : group⊆state.boulders) (bounded : group.length≤4) (holesInside : state.holes⊆soko1_1.initial.holes)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (pays : OwnedCorral11.PaidStep Side group dir t) :
 OwnedCorral11.Good Upper187Cover11.locks Upper187Cover11.region t.state (update group outcome) := by
 obtain ⟨i,heroInside,locksInside⟩ := good
 obtain ⟨source,owner,metadata,side⟩ := pays
 have member := complete i group bounded locksInside source owner
 have unblocked := WestRankHead11.source_unblocked head metadata (List.Subset.trans locksInside inside)
 have adjacent := PairPost11.source_adjacent head metadata
 have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
   (step_player_clear _ _ _ _ head).1 dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp transitions_checked i (by simp)) source member) dir (Geometry.all_directions dir)
 simp only [reverse] at row
 have shifted : CoverShift i source dir := by
   rcases of_decide_eq_true row with outside|blocked|notSide|shift
   · exact False.elim (outside heroInside)
   · exact False.elim (unblocked blocked)
   · exact False.elim (notSide side)
   · exact shift
 obtain ⟨j,dest,destFloor,targets,noHole,nextLocks,nextHero⟩ := shifted
 have outcomeEq := UpperHeadCases11.ordinary_effect head effect metadata targets noHole holesInside
 subst outcome
 have erased : (Parked18811.locks i).erase source⊆group.erase source :=
   GhostSubset.erase_subset locksInside (Parked18811.unique i) source
 refine ⟨j,?_,?_⟩
 · have player : t.state.player=source := by rw [effect.2]
   simpa only [player] using nextHero
 · simp only [update,move,if_pos owner,post]
   exact List.Subset.trans nextLocks (List.cons_subset_cons dest erased)

theorem first_cut {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bound : group.length≤4)
 (good : OwnedCorral11.Good Parked18811.locks Parked18811.region state group) :
 Nonempty (UpperFirstCut11.FirstCut paid state group dirs final pushes moves outcomes) := by
 rcases UpperFirstCut11.first_cut_or_quiet logged group with found|quiet
 · exact found
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have finalGood := PairFirstCut11.quiet_good closed Parked18811.unique Parked18811.size quiet valid.1 unique inside bound good reached.holes_sublist.subset
   obtain ⟨i,_,selected⟩ := finalGood
   have actual := (logged.end_subset valid.1 group unique inside).2
   have card := List.Nodup.length_le_of_subset (Parked18811.unique i) (List.Subset.trans selected actual)
   rw [Parked18811.size i] at card
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   omega
#print axioms head_shape
#print axioms enter_cover
#print axioms first_cut
end Owner1007.ParkedPivot11
