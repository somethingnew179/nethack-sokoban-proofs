import Owner1007.After264Pre18712
import Owner1007.Pocket290Gate12
import Owner1007.Park317Cash12
namespace Owner1007.After264Pre187Bound12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.After264Pre18712
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Base : List Cell := Core++[211,187]
def Bottom (i : Fin 5) : List Cell := [318,NorthEvents12.current i]
theorem perm : ∀ i,(Base++Bottom i).Perm (locks i) := by decide +kernel
theorem core_two_or_bottom_five
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 5)
 (hero : state.player∈region i) (subset : locks i⊆state.boulders)
 (zero187 : energy p [187] outcomes=0) :
 2≤energy p Core outcomes ∨5≤energy p (Bottom i) outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 rcases event_or_good closed unique logged reached (locks i) (unique i) subset hero (fun _ h=>h) with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroOne,inside,pays,unchanged⟩ :=
     event.split_fixed fixed fixed_inside
       (fun i hero h dir source found adjacent=>fixed_guard i hero h dir (Geometry.all_directions dir) source found adjacent)
       reached (unique i) subset
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have old := first.end_subset actualUnique (locks i) (unique i) subset
   have baseInside : Base⊆state.boulders := by
     have check : ∀ i,Base⊆locks i := by decide +kernel
     exact List.Subset.trans (check i) subset
   have bottomInside : Bottom i⊆state.boulders := by
     have check : ∀ i,Bottom i⊆locks i := by decide +kernel
     exact List.Subset.trans (check i) subset
   have bothUnique : (Base++Bottom i).Nodup := (perm i).nodup_iff.mpr (unique i)
   have bothInside : Base++Bottom i⊆state.boulders := List.append_subset.mpr ⟨baseInside,bottomInside⟩
   have splitBefore := first.end_split actualUnique Base (Bottom i) bothUnique bothInside
   have transport := endGroup_perm (perm i) before
   have split : (endGroup Base before++endGroup (Bottom i) before).Perm (endGroup (locks i) before) := splitBefore.trans transport
   have baseSame := unchanged Base (by decide +kernel)
   rw [baseSame] at split
   have bottomMember (cell : Cell) (member : cell∈locks j) (absent : cell∉Base) : cell∈endGroup (Bottom i) before := by
     have both := split.mem_iff.mpr (inside member)
     rcases List.mem_append.mp both with bad|found
     · exact False.elim (absent bad)
     · exact found
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,paidHead⟩ := pays
     have sourceLock : source∈locks j := by
       apply Classical.byContradiction
       intro absent
       have all : source::locks j⊆endGroup (locks i) before := by
         intro c found
         rcases List.mem_cons.mp found with rfl|found
         · exact owner
         · exact inside found
       have count := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨absent,unique j⟩) all
       have limit := endGroup_length_le (locks i) before
       rw [List.length_cons,size j] at count
       rw [size i] at limit
       omega
     obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
     rcases classification j middle.player heroOne dir (Geometry.all_directions dir) source sourceLock adjacent paidHead with blocked|core|upper|bottom
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans inside old.2) checked effect blocked)
     · obtain ⟨member,priced⟩ := core
       have prior := unchanged Core (by decide +kernel)
       have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked effect
       have bound := event_energy_le Generated.soko1_2_potential_valid Core first last (.push source ending)
       rw [prior] at bound
       simp only [projectedOutcome,if_pos member] at bound
       rw [←shape] at bound
       change slack p (.push source ending)≤energy p Core outcomes at bound
       exact Or.inl (by omega)
     · obtain ⟨rfl,north|south⟩ := upper
       · subst dir
         have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
           (show ∀ dest∈pushTargets soko1_2.board 187 .north,dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder 187 from by decide +kernel) checked effect
         have prior := unchanged [187] (by decide +kernel)
         have bound := event_energy_le Generated.soko1_2_potential_valid [187] first last (.push 187 ending)
         rw [prior] at bound
         simp only [projectedOutcome,if_pos (show (187:Cell)∈([187]:List Cell) by decide +kernel)] at bound
         rw [←shape] at bound
         change slack p (.push 187 ending)≤energy p [187] outcomes at bound
         omega
       · subst dir
         have sameEnding := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           (show pushTargets soko1_2.board 187 .south=[213] by decide +kernel) (by decide +kernel) checked effect
         subst ending
         have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
         have nextSubset := GhostSubset.update_subset middle t (.push 187 (.stay 213)) effect _ old.1 old.2
         have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
         have shifts : ∀ j,Pocket290Gate12.locks 0⊆213::(locks j).erase 187 := by decide +kernel
         have kept := CageFour12.shifted_inside (unique j) inside owner (shifts j)
         have physical := List.Subset.trans kept nextSubset
         have heroNext : t.state.player∈Pocket290Gate12.region 0 := by
           rw [matches_hero middle t (.push 187 (.stay 213)) effect]
           exact Pocket290Gate12.heroes 187 (by decide +kernel)
         have priorU := unchanged [187] (by decide +kernel)
         have splitU : energy p [187] outcomes=ownSlack p [187] before+energy p [213] after := by
           rw [shape,energy_at_split,priorU]
           have one : slack p (.push 187 (.stay 213))=0 := by decide +kernel
           simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true,one,Int.add_zero]
           rfl
         have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [187]
         have laterNN := last.energy_nonnegative Generated.soko1_2_potential_valid [213]
         change 0≤ownSlack p [187] before at nn
         change 0≤energy p [213] after at laterNN
         have zero213 : energy p [213] after=0 := by omega
         have later := Pocket290Gate12.ordinary_two last nextReached completed heroNext physical zero213
         change 2≤energy p Core after at later
         have priorCore := unchanged Core (by decide +kernel)
         have splitCore : energy p Core outcomes=ownSlack p Core before+energy p Core after := by
           rw [shape,energy_at_split,priorCore]
           have absent : (187:Cell)∉Core := by decide +kernel
           simp only [projectedOutcome,if_neg absent,slack,update,move,if_neg absent,Int.add_zero]
         have nnCore := first.ownSlack_nonnegative Generated.soko1_2_potential_valid Core
         change 0≤ownSlack p Core before at nnCore
         exact Or.inl (by omega)
     · obtain ⟨rfl,rfl⟩ := bottom
       have sameEnding := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have all318 : ∀ j,(318:Cell)∈locks j := by decide +kernel
       have allCurrent : ∀ j,NorthEvents12.current j∈locks j := by decide +kernel
       have allAway : ∀ j,NorthEvents12.current j∉Base := by decide +kernel
       have owner318 := bottomMember 318 (all318 j) (by decide +kernel)
       have current := bottomMember (NorthEvents12.current j) (allCurrent j) (allAway j)
       have currentMember : NorthEvents12.current j∈Park317Cash12.northCells := by
         have all : ∀ j,NorthEvents12.current j∈Park317Cash12.northCells := by decide +kernel
         exact all j
       have bottomUnique : (Bottom i).Nodup := by
         have all : ∀ i,(Bottom i).Nodup := by decide +kernel
         exact all i
       have five := Park317Cash12.group_five first checked effect last reached (Bottom i) bottomUnique bottomInside
         (NorthEvents12.current j) currentMember owner318 current
       change 5≤energy p (Bottom i) (before++.push 318 (.stay 317)::after) at five
       exact Or.inr (by rw [shape];exact five)
 · obtain ⟨j,_,kept⟩ := terminal
   have endInside := logged.end_subset actualUnique (locks i) (unique i) subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept endInside.2)
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms core_two_or_bottom_five
end Owner1007.After264Pre187Bound12
