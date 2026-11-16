import Owner1007.WestRank11
import NetHack.Sokoban.Reduction
import Owner1007.PairPost11
import Owner1007.UpperFirstCut11
import Owner1007.PairFirstCut11
namespace Owner1007.WestRankHead11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem source_unblocked {state : State} {dir : Dir} {t : Transition} {source : Cell} {locks : List Cell}
 (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source)
 (inside : locks⊆state.boulders) : ¬BlockedPush soko1_1.board locks source dir := by
 rcases step_cases_full _ _ _ _ head with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at metadata
   contradiction
 · obtain ⟨other,result,_,_,_,push,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using metadata
   subst other
   have first := push_first_clear _ _ _ _ _ push
   intro blocked
   rcases blocked with diagonal|blocked
   · simp only [first.1] at diagonal
     contradiction
   · obtain ⟨dest,next,floor,door,empty⟩ := first.2
     simp only [next] at blocked
     rcases blocked with wall|door'|box
     · exact wall floor
     · exact door door'
     · exact empty (inside box)

theorem lock_complete (i : Fin 15) (group : List Cell) (bounded : group.length≤3)
 (inside : WestRank11.locks i⊆group) (source : Cell) (owner : source∈group) :
 source∈WestRank11.locks i := by
 by_cases member : source∈WestRank11.locks i
 · exact member
 · have all : source::WestRank11.locks i⊆group := by
     intro c found
     rcases List.mem_cons.mp found with rfl|later
     · exact owner
     · exact inside later
   have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,WestRank11.unique i⟩) all
   simp only [List.length_cons,WestRank11.size i] at card
   omega

theorem head_shape {state : State} {group : List Cell} {dir : Dir} {t : Transition}
 (i : Fin 15) (heroInside : state.player∈WestRank11.region i) (locksInside : WestRank11.locks i⊆group)
 (inside : group⊆state.boulders) (bounded : group.length≤3)
 (head : step soko1_1.board state dir=some t)
 (pays : OwnedCorral11.PaidStep WestRank11.paid group dir t) :
 ∃source, source∈group ∧ t.pushSource=some source ∧ WestRank11.ExitShape i source dir := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 have member := lock_complete i group bounded locksInside source owner
 have actualLocks := List.Subset.trans locksInside inside
 have unblocked := source_unblocked head metadata actualLocks
 have adjacent := PairPost11.source_adjacent head metadata
 exact ⟨source,owner,metadata,WestRank11.exit_shape i state.player source dir heroInside member adjacent unblocked pays⟩

theorem first_cut {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good WestRank11.locks WestRank11.region state group) :
 Nonempty (UpperFirstCut11.FirstCut WestRank11.paid state group dirs final pushes moves outcomes) := by
 rcases UpperFirstCut11.first_cut_or_quiet logged group with found|quiet
 · exact found
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have finalGood := PairFirstCut11.quiet_good WestRank11.closed WestRank11.unique WestRank11.size quiet
     valid.1 groupUnique inside bounded good reached.holes_sublist.subset
   obtain ⟨i,_,selected⟩ := finalGood
   have actual := (logged.end_subset valid.1 group groupUnique inside).2
   have card := List.Nodup.length_le_of_subset (WestRank11.unique i) (List.Subset.trans selected actual)
   rw [WestRank11.size i] at card
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   omega

theorem marker216 (i : Fin 15) (present : 216∈WestRank11.locks i) : WestRank11.marker i=216 := by
 have all : (List.finRange 15).all (fun i => decide (216∈WestRank11.locks i → WestRank11.marker i=216))=true := by decide +kernel
 exact of_decide_eq_true (List.all_eq_true.mp all i (by simp)) present
theorem prices136 : (List.range 16).all (fun p => decide (ActorPrices11.price p 137 136 135=2))=true := by decide +kernel

theorem row136 {state : State} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t outcome)
 (metadata : t.pushSource=some 136) (owner : 136∈group) (unique : group.Nodup) (inside : group⊆state.boulders) :
 2≤RankedCorral11.gap state t group outcome := by
 obtain ⟨phase,atIndex⟩ := valid.2
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
     (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq]; exact atIndex
 have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
   HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
 have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1]; exact (List.drop_sublist phase _).subset
 have same := UpperHeadCases11.ordinary_effect head effect metadata (show pushTargets soko1_1.board 136 .west=[135] by decide +kernel)
   (by decide +kernel) holesInside
 subst outcome
 have hero := ActorPrices11.support_of_check 136 state.player .west 137 (by decide +kernel)
   (step_player_clear _ _ _ _ head).1 (PairPost11.source_adjacent head metadata)
 have price := of_decide_eq_true (List.all_eq_true.mp prices136 _ (List.mem_range.mpr active))
 have actor : 2≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 136 135-
     scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 136 := by
   rw [hero]
   exact Int.le_of_eq price.symm
 exact OwnedStrict11.owned_stay_bound scalar state .west t valid head 136 135 effect group unique inside owner 2 actor
#print axioms first_cut
#print axioms row136
#print axioms head_shape
end Owner1007.WestRankHead11
