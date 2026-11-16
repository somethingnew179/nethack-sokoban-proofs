import Owner1007.Upper187ForcedSouth12
import Owner1007.PriceTrap12
namespace Owner1007.Foreign184UpperFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks : Fin 3→List Cell
 | 0=>[108,158,159,186,187,184]
 | 1=>[108,158,159,160,187,184]
 | 2=>[108,158,159,134,184]
def base : List Cell := [115,116,117,140,141,142,143,163,164,166,167,168,169,185,189,190,191,192,193,194,210,211,212,213,214,215,216,218,219,220,236,237,238,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def region : Fin 3→List Cell |0=>base |1=>base++[186] |2=>base++[186,135,160,161,187]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=159∧dir=.north)∨(source=134∧dir=.west)∨(source=187∧dir=.north)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem large : ∀ i,2<(locks i).length := by decide +kernel
theorem hero210 : (210:Cell)∈region 0 := by decide +kernel
def upperIndex (i : Fin 3) : Fin 11 := if i=0 then 0 else if i=1 then 2 else 9
theorem upper_shift : ∀ i,UpperAfter18712.locks (upperIndex i)⊆161::(locks i).erase 187 := by decide +kernel
theorem upper_hero : ∀ i,(187:Cell)∈UpperAfter18712.region (upperIndex i) := by decide +kernel
theorem upper_credit : ∀ i,UpperAfter18712.credit (upperIndex i)=2 := by decide +kernel
theorem trap_shift159 : ∀ i,PriceTrap12.locks 0⊆133::(locks i).erase 159 := by decide +kernel
theorem trap_shift134 : ∀ i,PriceTrap12.locks 0⊆133::(locks i).erase 134 := by decide +kernel
theorem trap_hero : ∀ c∈([159,134]:List Cell),c∈PriceTrap12.region 0 := by decide +kernel
theorem trap_credit : ∀ i,PriceTrap12.credit i≤debtOf p (PriceTrap12.locks i) := by decide +kernel

theorem trap_eleven {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (hero : state.player∈PriceTrap12.region 0) (inside : PriceTrap12.locks 0⊆group) :
 11≤energy p group outcomes := by
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price PriceTrap12.closed PriceTrap12.unique
   logged reached group unique subset hero inside
 have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
   (PriceTrap12.locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
   (PriceTrap12.unique j) kept
 change debtOf p (PriceTrap12.locks j)≤debtOf p (endGroup group outcomes) at debt
 have credit := trap_credit j
 change 11≤ownSlack p group outcomes+PriceTrap12.credit j at price
 unfold energy
 omega

theorem energy_four {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 3}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 4≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays⟩ :=event.split
   have atReached := reached.append first.trace
   have old := first.end_subset actualUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ (atReached.boulders_nodup (by decide +kernel)) checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual _ old.1 old.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect _ old.1 old.2
   have nextReached := atReached.append (Trace.cons checked (Trace.nil t.state))
   have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at nn
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨owner,headPaid⟩:=pays
     have whole : energy p group outcomes=ownSlack p group before+slack p (.push source ending)+
       energy p (update (endGroup group before) (.push source ending)) after := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
     have headNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
     change 0≤slack p (.push source ending) at headNN
     rcases headPaid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 159 .north=[133] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (trap_shift159 j)
       have heroNext : t.state.player∈PriceTrap12.region 0 := by
         rw [matches_hero middle t (.push 159 (.stay 133)) effect]
         exact trap_hero 159 (by decide +kernel)
       have later := trap_eleven last nextReached _ nextUnique nextSubset heroNext kept
       change 11≤energy p (update (endGroup group before) (.push 159 (.stay 133))) after at later
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 134 .west=[133] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (trap_shift134 j)
       have heroNext : t.state.player∈PriceTrap12.region 0 := by
         rw [matches_hero middle t (.push 134 (.stay 133)) effect]
         exact trap_hero 134 (by decide +kernel)
       have later := trap_eleven last nextReached _ nextUnique nextSubset heroNext kept
       change 11≤energy p (update (endGroup group before) (.push 134 (.stay 133))) after at later
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (upper_shift j)
       have heroNext : t.state.player∈UpperAfter18712.region (upperIndex j) := by
         rw [matches_hero middle t (.push 187 (.stay 161)) effect]
         exact upper_hero j
       have later := UpperAfter18712.owned_energy_credit UpperAfter18712.matrix last nextReached
         _ nextUnique nextSubset heroNext kept
       rw [upper_credit] at later
       change 2≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
       have one : slack p (.push 187 (.stay 161))=2 := by decide +kernel
       rw [one] at whole
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept finalInside.2)
   have huge := large j
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms matrix
#print axioms energy_four
end Owner1007.Foreign184UpperFour12
