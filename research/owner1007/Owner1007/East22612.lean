import Owner1007.EastPrice225
import Owner1007.Final222
import Owner1007.FirstSplit12
import Owner1007.CageFour12
import Owner1007.RightPrice4
import Owner1007.TokenCounting
namespace Owner1007.East22612
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def trio : List Cell := [192,193,218]
theorem trio_inside : ∀ i, trio⊆EastCorral12.locks i := by decide +kernel
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
end Owner1007.East22612

namespace Owner1007.East22612
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem own_slack_split {board initial dirs final pushes moves outcomes}
 (logged : Logged board initial dirs final pushes moves outcomes)
 (actualUnique : initial.boulders.Nodup) (potential : Potential) (a b : List Cell)
 (unique : (a++b).Nodup) (subset : a++b⊆initial.boulders) :
 ownSlack potential (a++b) outcomes=ownSlack potential a outcomes+ownSlack potential b outcomes := by
 have e := logged.energy_split actualUnique potential a b unique subset
 have d := debtOf_perm potential (logged.end_split actualUnique a b unique subset)
 rw [debtOf_append] at d
 unfold energy at e
 omega
def eastWalk : Transition := {state := {soko1_2.initial with player:=370},pushed:=false,filled:=none}
def eastPush : Transition := {state:=EastPrice225.afterE,pushed:=true,filled:=none,pushSource:=some 371,landing:=some 372}
theorem east_reached : Trace soko1_2.board soko1_2.initial [.north,.east] EastPrice225.afterE 1 2 := by
 exact Trace.cons (next:=eastWalk) (by decide +kernel)
   (Trace.cons (next:=eastPush) (by decide +kernel) (Trace.nil _))
def G : List Cell := [372]++trio
theorem rank_credit : ∀ j : Fin 7, EastPrice225.locks j⊆[296]++trio → EastPrice225.credit j≤1 := by decide +kernel

theorem before_exit {dirs middle pushes moves before}
 (first : Logged soko1_2.board EastPrice225.afterE dirs middle pushes moves before)
 (fixed : endGroup trio before=trio) (zero : ownSlack p trio before=0)
 (owner : (296:Cell)∈endGroup G before) :
 5≤ownSlack p [372] before ∧ endGroup [372] before=[296] := by
 have initialUnique : EastPrice225.afterE.boulders.Nodup := by decide +kernel
 have split := first.end_split initialUnique [372] trio (by decide +kernel) (by decide +kernel)
 change (endGroup [372] before++endGroup trio before).Perm (endGroup G before) at split
 have member : (296:Cell)∈endGroup [372] before := by
   have old := split.mem_iff.mpr owner
   rw [fixed] at old
   rcases List.mem_append.mp old with found | found
   · exact found
   · exact False.elim ((by decide +kernel : (296:Cell)∉trio) found)
 have single : endGroup [372] before=[296] := by
   rcases singleton_end_shape 372 before with empty | ⟨cell,same⟩
   · exact False.elim (by simpa only [empty,List.not_mem_nil] using member)
   · have equal : 296=cell := by simpa only [same,List.mem_singleton] using member
     subst cell
     exact same
 have endPerm : ([296]++trio).Perm (endGroup G before) := by simpa only [single,fixed] using split
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price EastPrice225.closed EastPrice225.unique
   first east_reached G (by decide +kernel) (by decide +kernel)
   EastPrice225.afterE_good.1 (by decide +kernel)
 have small : EastPrice225.locks j⊆[296]++trio := fun c h => endPerm.mem_iff.mpr (kept h)
 have credit := rank_credit j small
 change 6≤ownSlack p G before+EastPrice225.credit j at price
 have slackSplit := own_slack_split first initialUnique p [372] trio (by decide +kernel) (by decide +kernel)
 change ownSlack p G before=ownSlack p [372] before+ownSlack p trio before at slackSplit
 exact ⟨by omega,single⟩
#print axioms own_slack_split
#print axioms before_exit
end Owner1007.East22612

namespace Owner1007.East22612
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem stone_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board EastPrice225.afterE dirs final pushes moves outcomes)
 (completed : Goal final) : 6≤energy p [372] outcomes := by
 have initialUnique : EastPrice225.afterE.boulders.Nodup := by decide +kernel
 rcases event_or_good EastCorral12.closed EastCorral12.unique logged east_reached G
   (by decide +kernel) (by decide +kernel) (i:=0) (by decide +kernel) (by decide +kernel) with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,heroOne,locksOne,pays,fixed,zero⟩ :=
     split_stationary event east_reached (by decide +kernel) (by decide +kernel)
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,pays⟩ := pays
     change source=296 ∧ dir=.north at pays
     obtain ⟨rfl,rfl⟩ := pays
     have middleReached := east_reached.append first.trace
     have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
       (show pushTargets soko1_2.board 296 .north=[270] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     obtain ⟨five,single⟩ := before_exit first fixed zero owner
     have later := last.energy_nonnegative Generated.soko1_2_potential_valid [270]
     change 0≤energy p [270] after at later
     have one : slack p (.push 296 (.stay 270))=1 := by decide +kernel
     rw [shape,energy_at_split,single]
     change 6≤ownSlack p [372] before+slack p (.push 296 (.stay 270))+energy p [270] after
     omega
 · obtain ⟨i,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset initialUnique G (by decide +kernel) (by decide +kernel)
   have count := List.Nodup.length_le_of_subset (EastCorral12.unique i) (List.Subset.trans locksOne finalInside.2)
   rw [EastCorral12.sizes i] at count
   have conserved := (east_reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega

theorem east_walk_checked : step soko1_2.board soko1_2.initial .north=some eastWalk := by decide +kernel
theorem east_push_checked : step soko1_2.board eastWalk.state .east=some eastPush := by decide +kernel
theorem east_walk_effect : Matches soko1_2.initial eastWalk (.walk 370) := rfl
theorem east_push_effect : Matches eastWalk.state eastPush (.push 371 (.stay 372)) := by
 refine ⟨by decide +kernel,?_⟩
 rfl

theorem canonical_east {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board EastPrice225.afterE dirs final pushes moves outcomes) :
 Logged soko1_2.board soko1_2.initial (.north::.east::dirs) final
   (1+pushes) (2+moves) (.walk 370::.push 371 (.stay 372)::outcomes) := by
 have first := Logged.cons east_push_checked east_push_effect logged
 have whole := Logged.cons east_walk_checked east_walk_effect first
 have moveEq : 1+(1+moves)=2+moves := by omega
 simpa [eastWalk,eastPush,Transition.pushCost,moveEq] using whole

theorem initial_stone_energy (outcomes : List Outcome) :
 energy p [371] (.walk 370::.push 371 (.stay 372)::outcomes)=2+energy p [372] outcomes := by
 rw [energy_cons]
 simp only [projectedOutcome,slack,update,Int.zero_add]
 rw [energy_cons]
 change slack p (.push 371 (.stay 372))+energy p [372] outcomes=2+energy p [372] outcomes
 have two : slack p (.push 371 (.stay 372))=2 := by decide +kernel
 rw [two]

theorem east_branch_logged_226 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board EastPrice225.afterE dirs final pushes moves outcomes)
 (completed : Goal final) : 226≤1+pushes := by
 have stone := stone_six logged completed
 have whole := canonical_east logged
 let all := .walk 370::.push 371 (.stay 372)::outcomes
 have stoneEight : (8:Int)≤energy p [371] all := by
   dsimp [all]
   rw [initial_stone_energy]
   omega
 have mono := whole.member_energy_le Generated.soko1_2_potential_valid (by decide +kernel)
   Final222.G (by decide +kernel) (by decide +kernel) 371 (by decide +kernel)
 change energy p [371] all≤energy p Final222.G all at mono
 have upper := Final222.upper_energy_two whole completed
 change 2≤energy p Final222.U all at upper
 have right := RightPrice4.right_energy_four whole completed
 change 4≤energy p Final222.R all at right
 have other := whole.energy_nonnegative Generated.soko1_2_potential_valid [213]
 change 0≤energy p [213] all at other
 have total := Final222.total_energy whole completed
 change energy p Final222.U all+energy p Final222.G all+energy p [213] all+energy p Final222.R all=
   Int.ofNat (1+pushes)-212 at total
 simp only [Int.ofNat_eq_natCast] at total
 omega

theorem east_branch_226 {dirs final pushes moves}
 (trace : Trace soko1_2.board FirstSplit12.afterE dirs final pushes moves)
 (completed : Goal final) : 226≤1+pushes := by
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact east_branch_logged_226 logged completed
#print axioms stone_six
#print axioms east_branch_226
end Owner1007.East22612

