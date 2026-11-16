import Owner1007.Post187BareNine12
import Owner1007.Vertical21223812
import Owner1007.Cage212Nine12
namespace Owner1007.Cage212RetainedEleven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def normal (i:Fin 4):Fin 6:=⟨i.val,by omega⟩
def oldIndex (i:Fin 6):Fin 10:=⟨i.val+4,by omega⟩
def locks (i:Fin 6):List Cell:=if i.val<4 then Cage10.locks (oldIndex i) else Cage21212.locks i
def region (i:Fin 6):List Cell:=if i.val<4 then Cage10.region (oldIndex i) else Cage21212.region i
def paid (source:Cell) (dir:Dir):Prop:=Cage21212.paid source dir∨source=238
instance (source:Cell) (dir:Dir):Decidable (paid source dir):=by unfold paid;infer_instance
def pushCheck (i:Fin 6) (source:Cell) (dir:Dir):Bool:=
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_2.board (locks i) source dir∨paid source dir∨
   Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
theorem push_rows:∀i,∀source∈locks i,∀dir∈allDirs,pushCheck i source dir=true:=by decide +kernel
theorem unique:∀i,(locks i).Nodup:=by decide +kernel
theorem floors:∀i,region i⊆soko1_2.board.floor:=by decide +kernel
theorem closed:PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid:=by
 constructor
 ·intro i hero member dir target adjacent floor door absent cornerClear
  by_cases small:i.val<4
  ·have old:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ Cage10.matrix
   have member':hero∈Cage10.region (oldIndex i):=by simpa only[region,if_pos small]using member
   have absent':target∉Cage10.locks (oldIndex i):=by simpa only[locks,if_pos small]using absent
   have corner':corner soko1_2.board (NetHack.Sokoban.PatternCorrection.project (Cage10.locks (oldIndex i))) hero dir=false:=by
    simpa only[locks,if_pos small]using cornerClear
   simpa only[region,if_pos small]using old.1 (oldIndex i) hero member' dir target adjacent floor door absent' corner'
  ·have member':hero∈Cage21212.region i:=by simpa only[region,if_neg small]using member
   have absent':target∉Cage21212.locks i:=by simpa only[locks,if_neg small]using absent
   have corner':corner soko1_2.board (NetHack.Sokoban.PatternCorrection.project (Cage21212.locks i)) hero dir=false:=by
    simpa only[locks,if_neg small]using cornerClear
   simpa only[region,if_neg small]using Cage21212.closed.1 i hero member' dir target adjacent floor door absent' corner'
 ·intro i hero member dir source sourceIn adjacent
  have back:=Geometry.reverseCheck_sound soko1_2.board Post187Seven12.reverse hero (floors i member) dir source adjacent
  have row:=push_rows i source sourceIn dir (Geometry.all_directions dir)
  simp only[pushCheck,back]at row
  rcases of_decide_eq_true row with outside|okay
  ·exact False.elim (outside member)
  ·exact okay
theorem badPair:∀i:Fin 6,4≤i.val→[210,236]⊆locks i∨[184,210]⊆locks i:=by decide +kernel
theorem normal_size:∀i:Fin 6,i.val<4→(locks i).length=10:=by decide +kernel
theorem max_size:∀i:Fin 6,(locks i).length≤10:=by decide +kernel
theorem upper_shift:∀i,Post187BareNine12.locks (Post187BareNine12.basic i)⊆161::(locks (normal i)).erase 187 ∧
 187∈Post187BareNine12.region (Post187BareNine12.basic i):=by decide +kernel
theorem quad_shift:∀i,BlockedPush soko1_2.board (locks (normal i)) 212 .west∨
 Quad211Trap12.locks 0⊆211::(locks (normal i)).erase 212:=by decide +kernel
theorem west_shift:∀i,237∈locks (normal i)→[210,236]⊆236::(locks (normal i)).erase 237:=by decide +kernel
theorem north_shift:∀i,211∈locks (normal i)→PriceTrap12Gate.locks 0⊆185::(locks (normal i)).erase 211∨
 [158,159,184,185]⊆185::(locks (normal i)).erase 211:=by decide +kernel
theorem upper_inside:∀i:Fin 4,CageLedger12.Upper⊆locks (normal i):=by decide +kernel
theorem pair_inside:∀i:Fin 4,[212,238]⊆locks (normal i):=by decide +kernel
theorem upper_bonus:RightEnergy12.cert.bonus 262 (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2:=by decide +kernel
theorem extra_check:∀i:Fin 4,∀hero∈region (normal i),∀dir∈allDirs,
 advance soko1_2.board hero dir=some 238→BlockedPush soko1_2.board (locks (normal i)) 238 dir∨dir=.east∨dir=.west:=by decide +kernel
theorem extra_shift:∀i:Fin 4,∀dir∈([.east,.west]:List Dir),∀dest∈pushTargets soko1_2.board 238 dir,
 Cage21212.locks (Cage212Nine12.normal i)⊆dest::(locks (normal i)).erase 238:=by decide +kernel
theorem extra_hero:∀i:Fin 4,(238:Cell)∈Cage21212.region (Cage212Nine12.normal i):=by decide +kernel
theorem extra_price:∀dir∈([.east,.west]:List Dir),∀dest∈pushTargets soko1_2.board 238 dir,
 dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder 238:=by decide +kernel
#print axioms push_rows
#print axioms closed
end Owner1007.Cage212RetainedEleven12

namespace Owner1007.Cage212RetainedEleven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem core_eleven {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 4)
 (hero : state.player∈Cage212RetainedEleven12.region (normal i))
 (subset : Cage212RetainedEleven12.locks (normal i)⊆state.boulders) :
 11≤energy p (Cage212RetainedEleven12.locks (normal i)) outcomes := by
 let group := Cage212RetainedEleven12.locks (normal i)
 change 11≤energy p group outcomes
 have gUnique := Cage212RetainedEleven12.unique (normal i)
 have initialUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good Cage212RetainedEleven12.closed Cage212RetainedEleven12.unique logged reached group gUnique subset hero
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
     have same : normal b=j := Fin.ext rfl
     have sourceMember (source : Cell) (owner : source∈endGroup group before) :
         source∈Cage212RetainedEleven12.locks j := by
       apply Classical.byContradiction
       intro outside
       have together : source::Cage212RetainedEleven12.locks j⊆endGroup group before := by
         intro c found
         rcases List.mem_cons.mp found with rfl|h
         · exact owner
         · exact locks h
       have count := List.Nodup.length_le_of_subset
         (List.nodup_cons.mpr ⟨outside,Cage212RetainedEleven12.unique j⟩) together
       have size := Cage212RetainedEleven12.normal_size j basic
       have max := endGroup_length_le group before
       have startSize : group.length=10 := Cage212RetainedEleven12.normal_size (normal i) i.isLt
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
           (shift : small⊆dest::(Cage212RetainedEleven12.locks j).erase source) :
           debtOf p small≤energy p (update (endGroup group before) (.push source ending)) after := by
         have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           targets clear checked effect
         subst ending
         have kept := CageFour12.shifted_inside (Cage212RetainedEleven12.unique j) locks owner shift
         exact last.locked_group_energy Generated.soko1_2_potential_valid nextActual
           (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
           small locked smallUnique kept
       rcases paid with original|sourceEq
       ·
         rcases original with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
         · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
             (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel)
             (by decide +kernel) checked effect
           subst ending
           obtain ⟨shift,newHero⟩ := upper_shift b
           rw [same] at shift
           have kept := CageFour12.shifted_inside (Cage212RetainedEleven12.unique j) locks owner shift
           have heroNext : t.state.player∈Post187BareNine12.region (Post187BareNine12.basic b) := by
             rw [matches_hero middle t (.push 187 (.stay 161)) effect]
             exact newHero
           have later := Post187BareNine12.energy_nine last nextReached
             (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset heroNext kept
           change 9≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
           exact reserve 2 9 (by decide +kernel) later
         · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
             (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
             (by decide +kernel) checked effect
           subst ending
           rcases quad_shift b with blocked|shift
           · rw [same] at blocked
             exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks oldGroup.2) checked effect blocked)
           · rw [same] at shift
             have kept := CageFour12.shifted_inside (Cage212RetainedEleven12.unique j) locks owner shift
             have heroNext : t.state.player∈Quad211Trap12.region 0 := by
               rw [matches_hero middle t (.push 212 (.stay 211)) effect]
               decide +kernel
             have later := Quad211Trap12.owned_energy_fifteen last nextReached
               (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset heroNext kept
             change 15≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
             have bound := reserve 0 15 oneNN later
             omega
         · have memberB : 237∈Cage212RetainedEleven12.locks (normal b) := by simpa only [same] using member
           have shift := west_shift b memberB
           rw [same] at shift
           have later := lockedBound 236 [210,236] (by decide +kernel) (by decide +kernel)
             (by decide +kernel) CageLedger12.locked_210236 shift
           have amount : (11:Int)≤debtOf p [210,236] := by decide +kernel
           have bound := reserve 0 (debtOf p [210,236]) oneNN later
           omega
         · have memberB : 211∈Cage212RetainedEleven12.locks (normal b) := by simpa only [same] using member
           rcases north_shift b memberB with gate|square
           · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
               (show pushTargets soko1_2.board 211 .north=[185] by decide +kernel)
               (by decide +kernel) checked effect
             subst ending
             rw [same] at gate
             have kept := CageFour12.shifted_inside (Cage212RetainedEleven12.unique j) locks owner gate
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
         · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
             (show pushTargets soko1_2.board 262 .south=[288] by decide +kernel)
             (by decide +kernel) checked effect
           subst ending
           have uBefore : CageLedger12.Upper⊆endGroup group before := by
             have h := upper_inside b
             rw [same] at h
             exact List.Subset.trans h locks
           have uAfter := update_mono CageLedger12.Upper (endGroup group before)
             (by decide +kernel) uBefore (.push 262 (.stay 288))
           simp only [update,move,if_neg (show (262:Cell)∉CageLedger12.Upper by decide +kernel)] at uAfter
           have uActual := List.Subset.trans uAfter nextSubset
           have upper := RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper
             (by decide +kernel) uActual completed
           rw [matches_hero middle t (.push 262 (.stay 288)) effect] at upper
           change RightEnergy12.cert.bonus 262
             (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)≤energy p CageLedger12.Upper after at upper
           rw [upper_bonus] at upper
           have pairBefore : ([212,238]:List Cell)⊆endGroup group before:=by
             have h:=pair_inside b
             rw[same] at h
             exact List.Subset.trans h locks
           have pairAfter:=update_mono ([212,238]:List Cell) (endGroup group before) (by decide +kernel) pairBefore (.push 262 (.stay 288))
           simp only[update,move,if_neg (show (262:Cell)∉([212,238]:List Cell) by decide +kernel)] at pairAfter
           have pairHero:t.state.player∈Vertical21223812.region 0:=by
             rw[matches_hero middle t (.push 262 (.stay 288)) effect]
             decide +kernel
           have v:=Vertical21223812.owned_energy_two last nextReached [212,238] (by decide +kernel)
             (List.Subset.trans pairAfter nextSubset) pairHero (fun _ h=>h)
           change 2≤energy p [212,238] after at v
           have add:=TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual
             CageLedger12.Upper [212,238] (update (endGroup group before) (.push 262 (.stay 288)))
             (by decide +kernel) nextUnique nextSubset (List.append_subset.mpr ⟨uAfter,pairAfter⟩)
           change energy p CageLedger12.Upper after+energy p [212,238] after≤
             energy p (update (endGroup group before) (.push 262 (.stay 288))) after at add
           have later:4≤energy p (update (endGroup group before) (.push 262 (.stay 288))) after:=by omega
           exact reserve 7 4 (by decide +kernel) later

       ·subst source
        obtain ⟨_,adjacent,_⟩:=effect_push_data checked effect
        have heroB:middle.player∈region (normal b):=by simpa only[same] using heroBefore
        rcases extra_check b middle.player heroB dir (Geometry.all_directions dir) adjacent with blocked|e|w
        ·rw[same] at blocked
         exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks oldGroup.2) checked effect blocked)
        all_goals
         have memberDir:dir∈([.east,.west]:List Dir):=by simp_all
         have price:=push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
           (extra_price dir memberDir) checked effect
         have oldBefore:Cage21212.locks (Cage212Nine12.normal b)⊆endGroup group before:=by
           have finite:∀i,Cage21212.locks (Cage212Nine12.normal i)⊆Cage212RetainedEleven12.locks (normal i):=by decide +kernel
           have shift:=finite b
           rw[same] at shift
           exact List.Subset.trans shift locks
         have oldAfter:=update_mono (Cage21212.locks (Cage212Nine12.normal b)) (endGroup group before)
           (Cage21212.unique _) oldBefore (.push 238 ending)
         have absent:(238:Cell)∉Cage21212.locks (Cage212Nine12.normal b):=by
           have finite:∀i,(238:Cell)∉Cage21212.locks (Cage212Nine12.normal i):=by decide +kernel
           exact finite b
         simp only[update,move,if_neg absent] at oldAfter
         have heroNext:t.state.player∈Cage21212.region (Cage212Nine12.normal b):=by
           rw[matches_hero middle t (.push 238 ending) effect]
           exact extra_hero b
         have later:=Cage212Nine12.energy_nine last nextReached _ nextUnique nextSubset completed b heroNext oldAfter
         change 9≤energy p (update (endGroup group before) (.push 238 ending)) after at later
         have bound:=reserve 2 9 price later
         omega
   · have large : 4≤j.val := by omega
     have pair := Cage212RetainedEleven12.badPair j large
     have rest : Logged soko1_2.board middle (dir::afterDirs) final (t.pushCost+afterPushes) (1+afterMoves)
       (outcome::after) := .cons checked effect last
     have lockedBound (small : List Cell) (smallUnique : small.Nodup) (locked : Locked soko1_2.board small)
         (kept : small⊆Cage212RetainedEleven12.locks j) :
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
   · have count := List.Nodup.length_le_of_subset (Cage212RetainedEleven12.unique j) (List.Subset.trans kept finalInside.2)
     have amount := Cage212RetainedEleven12.normal_size j basic
     have conserved := (reached.append logged.trace).conservation
     have empty : final.holes=[] := completed
     change 20+final.holes.length=final.boulders.length+18 at conserved
     rw [empty] at conserved
     simp only [List.length_nil] at conserved
     omega
   · have large : 4≤j.val := by omega
     have pair := Cage212RetainedEleven12.badPair j large
     have nn := logged.ownSlack_nonnegative Generated.soko1_2_potential_valid group
     change 0≤ownSlack p group outcomes at nn
     have debtBound (small : List Cell) (smallUnique : small.Nodup) (smallInside : small⊆Cage212RetainedEleven12.locks j) :
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
 (hero : state.player∈Cage212RetainedEleven12.region (normal i)) (inside : Cage212RetainedEleven12.locks (normal i)⊆group) :
 11≤energy p group outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have smallActual := List.Subset.trans inside subset
 have bound := core_eleven logged reached completed i hero smallActual
 have mono := logged.energy_mono Generated.soko1_2_potential_valid actualUnique
   (Cage212RetainedEleven12.locks (normal i)) group (Cage212RetainedEleven12.unique _) gUnique smallActual subset inside
 change energy p (Cage212RetainedEleven12.locks (normal i)) outcomes≤energy p group outcomes at mono
 omega
#print axioms energy_eleven
end Owner1007.Cage212RetainedEleven12
