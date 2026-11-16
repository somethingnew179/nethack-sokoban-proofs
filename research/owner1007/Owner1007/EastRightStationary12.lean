import Owner1007.EastPrice225
import Owner1007.CageFour12
import Owner1007.RightPrice4
import Owner1007.TokenCounting
namespace Owner1007.EastRightStationary12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def trio : List Cell := RightEnergy12.Right
theorem trio_guard : ∀ i, ∀ hero∈EastCorral12.region i, ∀ dir∈allDirs, ∀ source∈trio,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (EastCorral12.locks i) source dir := by decide +kernel

theorem stationary_step {state dir t outcome i}
 (hero : state.player∈EastCorral12.region i)
 (inside : EastCorral12.locks i⊆state.boulders)
 (checked : step soko1_2.board state dir=some t) (effect : Matches state t outcome) :
 update trio outcome=trio ∧ slack p (projectedOutcome trio outcome)=0 := by
 cases outcome with
 | walk target => exact ⟨rfl,rfl⟩
 | push source ending =>
   have absent : source∉trio := by
     intro member
     obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
     exact CageFour12.blocked_impossible inside checked effect
       (trio_guard i state.player hero dir (Geometry.all_directions dir) source member adjacent)
   simp [update,move,absent,projectedOutcome,slack]

theorem split_stationary
 {group state dirs final pushes moves outcomes}
 (event : EventLog EastCorral12.locks EastCorral12.region EastCorral12.paid group state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (unique : group.Nodup) (subset : group⊆state.boulders) :
 ∃ beforeDirs beforePushes beforeMoves before middle dir t outcome after
   afterDirs afterPushes afterMoves, ∃ i : Fin 6,
   outcomes=before++outcome::after ∧
   Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
   step soko1_2.board middle dir=some t ∧ Matches middle t outcome ∧
   Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
   middle.player∈EastCorral12.region i ∧ EastCorral12.locks i⊆endGroup group before ∧
   PaidOutcome EastCorral12.paid dir (endGroup group before) outcome ∧
   endGroup trio before=trio ∧ ownSlack p trio before=0 := by
 induction event generalizing history past pastMoves with
 | @head group state dir t rest final pushes moves outcome outcomes i hero locks checked effect pays tail =>
   exact ⟨[],0,0,[],state,dir,t,outcome,outcomes,rest,pushes,moves,i,
     rfl,.nil state,checked,effect,tail,hero,locks,pays,rfl,rfl⟩
 | @tail group state dir t rest final pushes moves outcome outcomes i hero locks checked effect avoid later ih =>
   have actualUnique := reached.boulders_nodup (by decide +kernel)
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
   have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
   have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
   have one := stationary_step hero (List.Subset.trans locks subset) checked effect
   obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,payDir,u,payOutcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checkedOne,effectOne,last,heroOne,locksOne,pays,unchanged,zero⟩ :=
     ih nextReached nextUnique nextSubset
   refine ⟨dir::beforeDirs,t.pushCost+beforePushes,1+beforeMoves,outcome::before,
     middle,payDir,u,payOutcome,after,afterDirs,afterPushes,afterMoves,j,?_,
     .cons checked effect first,checkedOne,effectOne,last,heroOne,locksOne,pays,?_,?_⟩
   · simp only [List.cons_append,shape]
   · change endGroup (update trio outcome) before=trio
     rw [one.1]
     exact unchanged
   · change slack p (projectedOutcome trio outcome)+ownSlack p (update trio outcome) before=0
     rw [one.1,one.2,zero]
     rfl
#print axioms stationary_step
#print axioms split_stationary
end Owner1007.EastRightStationary12

