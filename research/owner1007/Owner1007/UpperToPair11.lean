import Owner1007.UpperFirstCut11
import Owner1007.PairFirstCut11
import Owner1007.PairPost11
namespace Owner1007.UpperToPair11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem step_avoid {state : State} {big small : List Cell} {dir : Dir} {t : Transition}
 (good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state big)
 (bounded : big.length≤3) (subset : small⊆big)
 (head : step soko1_1.board state dir=some t)
 (avoid : ¬OwnedCorral11.PaidStep UpperZero11.paid big dir t) :
 ¬OwnedCorral11.PaidStep PairPath11.paid small dir t := by
 intro pays
 obtain ⟨source,owner,metadata,pays⟩ := pays
 have inBig := subset owner
 rcases pays with h|h|h|h|⟨rfl,rfl⟩|h
 · exact avoid ⟨source,inBig,metadata,by simp [UpperZero11.paid,h.1,h.2]⟩
 · exact avoid ⟨source,inBig,metadata,by simp [UpperZero11.paid,h.1,h.2]⟩
 · exact avoid ⟨source,inBig,metadata,by simp [UpperZero11.paid,h.1,h.2]⟩
 · exact avoid ⟨source,inBig,metadata,by simp [UpperZero11.paid,h.1,h.2]⟩
 · obtain ⟨i,heroInside,locksInside⟩ := good
   have sourceLock := UpperQuiet11.lock_complete i big bounded locksInside 112 inBig
   have hero := ActorPrices11.support_of_check 112 state.player .east 111 (by decide +kernel)
     (step_player_clear _ _ _ _ head).1 (PairPost11.source_adjacent head metadata)
   have all : (List.finRange 19).all (fun i => decide (112∈UpperZero11.locks i → 111∉UpperZero11.region i))=true := by decide +kernel
   have excluded := of_decide_eq_true (List.all_eq_true.mp all i (by simp)) sourceLock
   exact excluded (by simpa only [hero] using heroInside)
 · exact avoid ⟨source,inBig,metadata,by simp [UpperZero11.paid,h.1,h.2]⟩

theorem quiet_project {state final : State} {big : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet UpperZero11.paid state big dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (bigUnique : big.Nodup) (inside : big⊆state.boulders)
 (bounded : big.length≤3) (good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state big)
 (holesInside : state.holes⊆soko1_1.initial.holes)
 (small : List Cell) (smallUnique : small.Nodup) (subset : small⊆big) :
 UpperQuiet11.Quiet PairPath11.paid state small dirs final pushes moves outcomes := by
 induction quiet generalizing small with
 | nil => exact .nil _ _
 | @cons state big dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   have smallInside := List.Subset.trans subset inside
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
   have nextBigUnique := GhostSubset.update_unique _ _ _ effect nextActual big bigUnique inside
   have nextBigInside := GhostSubset.update_subset _ _ _ effect big bigUnique inside
   have nextBound := Nat.le_trans (update_length big outcome) bounded
   have nextGood := OwnedCorral11.step_good_except UpperZero11.closed UpperZero11.unique UpperZero11.size good inside bounded holesInside head effect avoid
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
   have nextSmallUnique := GhostSubset.update_unique _ _ _ effect nextActual small smallUnique smallInside
   have nextSubset := update_mono small big smallUnique subset outcome
   have noPair := step_avoid good bounded subset head avoid
   exact .cons head effect noPair
     (ih nextActual nextBigUnique nextBigInside nextBound nextGood nextHoles (update small outcome) nextSmallUnique nextSubset)

theorem before_pair {dirs final pushes moves outcomes}
 (cut : UpperFirstCut11.FirstCut UpperZero11.paid soko1_1.initial UpperFirstCut11.originalGroup dirs final pushes moves outcomes) :
 UpperQuiet11.Quiet PairPath11.paid soko1_1.initial PairFirstCut11.originalGroup cut.beforeDirs cut.middle
   cut.beforePushes cut.beforeMoves cut.beforeOutcomes :=
 quiet_project cut.before (by decide) (by decide) (by decide) (by decide) UpperFirstCut11.original_good
   (by simp) PairFirstCut11.originalGroup (by decide) (by decide)

def as_pair {dirs final pushes moves outcomes}
 (cut : UpperFirstCut11.FirstCut UpperZero11.paid soko1_1.initial UpperFirstCut11.originalGroup dirs final pushes moves outcomes)
 (pays : OwnedCorral11.PaidStep PairPath11.paid (endGroup PairFirstCut11.originalGroup cut.beforeOutcomes) cut.direction cut.actor) :
 UpperFirstCut11.FirstCut PairPath11.paid soko1_1.initial PairFirstCut11.originalGroup dirs final pushes moves outcomes :=
 { middle:=cut.middle,actor:=cut.actor,direction:=cut.direction,headOutcome:=cut.headOutcome,
   beforeDirs:=cut.beforeDirs,beforePushes:=cut.beforePushes,beforeMoves:=cut.beforeMoves,beforeOutcomes:=cut.beforeOutcomes,
   afterDirs:=cut.afterDirs,afterPushes:=cut.afterPushes,afterMoves:=cut.afterMoves,afterOutcomes:=cut.afterOutcomes,
   before:=before_pair cut,headChecked:=cut.headChecked,headEffect:=cut.headEffect,headPaid:=pays,
   after:=cut.after,dirsEq:=cut.dirsEq,outcomesEq:=cut.outcomesEq,pushesEq:=cut.pushesEq,movesEq:=cut.movesEq }
#print axioms before_pair
end Owner1007.UpperToPair11
