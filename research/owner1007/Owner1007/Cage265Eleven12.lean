import Owner1007.Cage265Nine12
import Owner1007.Cage239Eleven12
import Owner1007.Cage212RetainedEleven12
import Owner1007.PreAccessNineFour12
namespace Owner1007.Cage265Eleven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def tIndex (i:Fin 4):Fin 10:=⟨i.val,by omega⟩
def fourIndex (i:Fin 4):Fin 2:=⟨i.val%2,by omega⟩
def fourFrame (i:Fin 4):List Cell:=
 if i.val<2 then PreAccessNineFour12.locks (fourIndex i) else Foreign184UpperFour12.locks 0
theorem four_shift:∀i,fourFrame i⊆288::(Cage265Retained12.locks (Cage265Retained12.normal i)).erase 262:=by decide +kernel
theorem four_hero:∀i:Fin 2,(262:Cell)∈PreAccessNineFour12.region i:=by decide +kernel
theorem foreign_hero:(262:Cell)∈Foreign184UpperFour12.region 0:=by decide +kernel
theorem s_shift:∀i,Cage212RetainedEleven12.locks (Cage212RetainedEleven12.normal i)⊆
 212::(Cage265Retained12.locks (Cage265Retained12.normal i)).erase 213 ∧
 213∈Cage212RetainedEleven12.region (Cage212RetainedEleven12.normal i):=by decide +kernel
theorem t_shift:∀i,Cage23912.locks (tIndex i)⊆239::(Cage265Retained12.locks (Cage265Retained12.normal i)).erase 265 ∧
 265∈Cage23912.region (tIndex i):=by decide +kernel
theorem four_at262 {state final dirs pushes moves outcomes history past pastMoves}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (unique:group.Nodup) (subset:group⊆state.boulders) (completed:Goal final)
 (i:Fin 4) (hero:state.player=262) (inside:fourFrame i⊆group):4≤energy p group outcomes:=by
 by_cases small:i.val<2
 ·have kept:PreAccessNineFour12.locks (fourIndex i)⊆group:=by simpa only[fourFrame,if_pos small]using inside
  have heroNext:state.player∈PreAccessNineFour12.region (fourIndex i):=by rw[hero];exact four_hero _
  exact PreAccessNineFour12.energy_four logged reached group unique subset completed heroNext kept
 ·have kept:Foreign184UpperFour12.locks 0⊆group:=by simpa only[fourFrame,if_neg small]using inside
  have heroNext:state.player∈Foreign184UpperFour12.region 0:=by rw[hero];exact foreign_hero
  exact Foreign184UpperFour12.energy_four logged reached group unique subset completed heroNext kept
theorem core_eleven {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 4)
 (hero : state.player∈Cage265Retained12.region (Cage265Retained12.normal i))
 (subset : Cage265Retained12.locks (Cage265Retained12.normal i)⊆state.boulders) :
 11≤energy p (Cage265Retained12.locks (Cage265Retained12.normal i)) outcomes := by
 let group := Cage265Retained12.locks (Cage265Retained12.normal i)
 change 11≤energy p group outcomes
 have gUnique := Cage265Retained12.unique (Cage265Retained12.normal i)
 have initialUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good Cage265Retained12.closed Cage265Retained12.unique logged reached group gUnique subset hero
   (fun _ h=>h) with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locks,pays⟩ := event.split
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have oldGroup := first.end_subset initialUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
   have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at prefixNN
   by_cases basic : j.val<4
   · let b : Fin 4 := ⟨j.val,basic⟩
     have same : Cage265Retained12.normal b=j := Fin.ext rfl
     have sourceMember (source : Cell) (owner : source∈endGroup group before) :
         source∈Cage265Retained12.locks j := by
       apply Classical.byContradiction
       intro outside
       have together : source::Cage265Retained12.locks j⊆endGroup group before := by
         intro c found
         rcases List.mem_cons.mp found with rfl|h
         · exact owner
         · exact locks h
       have count := List.Nodup.length_le_of_subset
         (List.nodup_cons.mpr ⟨outside,Cage265Retained12.unique j⟩) together
       have size := Cage265Retained12.normal_size j basic
       have max := endGroup_length_le group before
       have startSize : group.length=11 := Cage265Retained12.normal_size (Cage265Retained12.normal i) i.isLt
       simp only [List.length_cons] at count
       omega
     cases outcome with
     | walk target => exact False.elim pays
     | push source ending =>
       obtain ⟨owner,paid⟩ := pays
       have member := sourceMember source owner
       have oneNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
       have reserve (a b : Int) (one : a≤slack p (.push source ending))
           (later : b≤energy p (update (endGroup group before) (.push source ending)) after) :
           a+b≤energy p group outcomes := by
         rw [shape,energy_at_split]
         simp only [projectedOutcome,if_pos owner]
         omega
       have lockedBound (dest : Cell) (small : List Cell)
           (targets : pushTargets soko1_2.board source dir=[dest])
           (clear : dest∉soko1_2.initial.holes)
           (smallUnique : small.Nodup) (locked : Locked soko1_2.board small)
           (shift : small⊆dest::(Cage265Retained12.locks j).erase source) :
           debtOf p small≤energy p (update (endGroup group before) (.push source ending)) after := by
         have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           targets clear checked effect
         subst ending
         have kept := CageFour12.shifted_inside (Cage265Retained12.unique j) locks owner shift
         exact last.locked_group_energy Generated.soko1_2_potential_valid nextActual
           (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
           small locked smallUnique kept
       rcases paid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
       · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           (show pushTargets soko1_2.board 213 .west=[212] by decide +kernel)
           (by decide +kernel) checked effect
         subst ending
         obtain ⟨shift,newHero⟩ := s_shift b
         rw [same] at shift
         have kept := CageFour12.shifted_inside (Cage265Retained12.unique j) locks owner shift
         have heroNext : t.state.player∈Cage212RetainedEleven12.region (Cage212RetainedEleven12.normal b) := by
           rw [matches_hero middle t (.push 213 (.stay 212)) effect]
           exact newHero
         have later := Cage212RetainedEleven12.energy_eleven last nextReached
           (update (endGroup group before) (.push 213 (.stay 212))) nextUnique nextSubset completed b heroNext kept
         change 11≤energy p (update (endGroup group before) (.push 213 (.stay 212))) after at later
         exact reserve 0 11 oneNN later
       · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           (show pushTargets soko1_2.board 265 .north=[239] by decide +kernel)
           (by decide +kernel) checked effect
         subst ending
         obtain ⟨shift,newHero⟩ := t_shift b
         rw [same] at shift
         have kept := CageFour12.shifted_inside (Cage265Retained12.unique j) locks owner shift
         have heroNext : t.state.player∈Cage23912.region (tIndex b) := by
           rw [matches_hero middle t (.push 265 (.stay 239)) effect]
           exact newHero
         have later := Cage239Eleven12.energy_eleven last nextReached
           (update (endGroup group before) (.push 265 (.stay 239))) nextUnique nextSubset completed heroNext kept
         change 11≤energy p (update (endGroup group before) (.push 265 (.stay 239))) after at later
         exact reserve 0 11 oneNN later
       · have shift := Cage265Retained12.pair_shift b
         rw [same] at shift
         have later := lockedBound 239 [239,265] (by decide +kernel) (by decide +kernel)
           (by decide +kernel) Cage265Retained12.locked_pair shift
         have amount : (11:Int)≤debtOf p [239,265] := by decide +kernel
         have bound := reserve 0 (debtOf p [239,265]) oneNN later
         omega
       · have memberB : 238∈Cage265Retained12.locks (Cage265Retained12.normal b) := by simpa only [same] using member
         have shift := Cage265Retained12.square_shift b 238 (by decide +kernel) memberB
         rw [same] at shift
         have later := lockedBound 212 [186,187,212,213] (by decide +kernel) (by decide +kernel)
           (by decide +kernel) CageLedger12.locked_middle_square shift
         have amount : (11:Int)≤debtOf p [186,187,212,213] := by decide +kernel
         have bound := reserve 0 (debtOf p [186,187,212,213]) oneNN later
         omega
       · have memberB : 211∈Cage265Retained12.locks (Cage265Retained12.normal b) := by simpa only [same] using member
         rcases Cage265Retained12.gate_shift b memberB with gate|square
         · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
             (show pushTargets soko1_2.board 211 .north=[185] by decide +kernel)
             (by decide +kernel) checked effect
           subst ending
           rw [same] at gate
           have kept := CageFour12.shifted_inside (Cage265Retained12.unique j) locks owner gate
           have heroNext : t.state.player∈PriceTrap12Gate.region 0 := by
             rw [matches_hero middle t (.push 211 (.stay 185)) effect]
             decide +kernel
           have later := CageLedger12.gate_owned_nineteen last nextReached
             (update (endGroup group before) (.push 211 (.stay 185))) nextUnique nextSubset heroNext kept
           change 19≤energy p (update (endGroup group before) (.push 211 (.stay 185))) after at later
           have bound := reserve 0 19 oneNN later
           omega
         · rw [same] at square
           have later := lockedBound 185 [158,159,184,185] (by decide +kernel) (by decide +kernel)
             (by decide +kernel) CageLedger12.locked_upper_square square
           have amount : (11:Int)≤debtOf p [158,159,184,185] := by decide +kernel
           have bound := reserve 0 (debtOf p [158,159,184,185]) oneNN later
           omega
       · have memberB : 211∈Cage265Retained12.locks (Cage265Retained12.normal b) := by simpa only [same] using member
         have shift := Cage265Retained12.square_shift b 211 (by decide +kernel) memberB
         rw [same] at shift
         have later := lockedBound 212 [186,187,212,213] (by decide +kernel) (by decide +kernel)
           (by decide +kernel) CageLedger12.locked_middle_square shift
         have amount : (11:Int)≤debtOf p [186,187,212,213] := by decide +kernel
         have bound := reserve 0 (debtOf p [186,187,212,213]) oneNN later
         omega
       · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           (show pushTargets soko1_2.board 262 .south=[288] by decide +kernel)
           (by decide +kernel) checked effect
         subst ending
         have shift:=four_shift b
         rw[same]at shift
         have kept:=CageFour12.shifted_inside (Cage265Retained12.unique j) locks owner shift
         have heroNext:t.state.player=262:=matches_hero middle t (.push 262 (.stay 288)) effect
         have later:=four_at262 last nextReached _ nextUnique nextSubset completed b heroNext kept
         have bound:=reserve 7 4 (by decide +kernel) later
         omega
   · have large : 4≤j.val := by omega
     have pair := Cage265Retained12.badPair j large
     have rest : Logged soko1_2.board middle (dir::afterDirs) final (t.pushCost+afterPushes) (1+afterMoves)
       (outcome::after) := .cons checked effect last
     have lockedBound (small : List Cell) (smallUnique : small.Nodup) (locked : Locked soko1_2.board small)
         (kept : small⊆Cage265Retained12.locks j) :
         debtOf p small≤energy p (endGroup group before) (outcome::after) :=
       rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique (endGroup group before)
         oldGroup.1 oldGroup.2 small locked smallUnique (List.Subset.trans kept locks)
     rcases pair with left|right
     · have later := lockedBound [210,236] (by decide +kernel) CageLedger12.locked_210236 left
       have amount : (11:Int)≤debtOf p [210,236] := by decide +kernel
       rw [shape,TokenAccounting.energy_append]
       omega
     · have later := lockedBound [184,210] (by decide +kernel) CageLedger12.locked_184210 right
       have amount : (11:Int)≤debtOf p [184,210] := by decide +kernel
       rw [shape,TokenAccounting.energy_append]
       omega
 · obtain ⟨j,heroEnd,kept⟩ := terminal
   have finalInside := logged.end_subset initialUnique group gUnique subset
   by_cases basic : j.val<4
   · have count := List.Nodup.length_le_of_subset (Cage265Retained12.unique j) (List.Subset.trans kept finalInside.2)
     have amount := Cage265Retained12.normal_size j basic
     have conserved := (reached.append logged.trace).conservation
     have empty : final.holes=[] := completed
     change 20+final.holes.length=final.boulders.length+18 at conserved
     rw [empty] at conserved
     simp only [List.length_nil] at conserved
     omega
   · have large : 4≤j.val := by omega
     have pair := Cage265Retained12.badPair j large
     have nn := logged.ownSlack_nonnegative Generated.soko1_2_potential_valid group
     change 0≤ownSlack p group outcomes at nn
     have debtBound (small : List Cell) (smallUnique : small.Nodup) (smallInside : small⊆Cage265Retained12.locks j) :
         debtOf p small≤debtOf p (endGroup group outcomes) :=
       NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c) small (endGroup group outcomes)
         (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c≤0 at h; omega)
         smallUnique (List.Subset.trans smallInside kept)
     rcases pair with left|right
     · have debt := debtBound [210,236] (by decide +kernel) left
       have amount : (11:Int)≤debtOf p [210,236] := by decide +kernel
       unfold energy
       omega
     · have debt := debtBound [184,210] (by decide +kernel) right
       have amount : (11:Int)≤debtOf p [184,210] := by decide +kernel
       unfold energy
       omega

theorem energy_eleven {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (i : Fin 4)
 (hero : state.player∈Cage265Retained12.region (Cage265Retained12.normal i)) (inside : Cage265Retained12.locks (Cage265Retained12.normal i)⊆group) :
 11≤energy p group outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have smallActual := List.Subset.trans inside subset
 have bound := core_eleven logged reached completed i hero smallActual
 have mono := logged.energy_mono Generated.soko1_2_potential_valid actualUnique
   (Cage265Retained12.locks (Cage265Retained12.normal i)) group (Cage265Retained12.unique _) gUnique smallActual subset inside
 change energy p (Cage265Retained12.locks (Cage265Retained12.normal i)) outcomes≤energy p group outcomes at mono
 omega
#print axioms energy_eleven
end Owner1007.Cage265Eleven12
