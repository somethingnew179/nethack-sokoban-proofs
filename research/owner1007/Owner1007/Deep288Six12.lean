import Owner1007.PreAccessNineFour12
import Owner1007.Ring28812
namespace Owner1007.Deep288Six12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def locks (i:Fin 2):List Cell:=[108,158,159,186,187,210,237,238,263,213,if i.val=0 then 265 else 239,288]
def base:List Cell:=[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,264,270,271,272,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def region (i:Fin 2):List Cell:=if i.val=0 then base else base++[265]
def paid (source:Cell) (dir:Dir):Prop:=
 (source=263∧dir=.west)∨(source=213∧dir=.west)∨(source=238∧dir=.north)
instance (source:Cell) (dir:Dir):Decidable (paid source dir):=by unfold paid;infer_instance
theorem matrix:PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true:=by decide +kernel
theorem unique:∀i,(locks i).Nodup:=by decide +kernel
theorem size:∀i,(locks i).length=12:=by decide +kernel
theorem h9_shift:∀i,PreAccessNineFour12.locks 0⊆262::(locks i).erase 263:=by decide +kernel
theorem h9_hero:(263:Cell)∈PreAccessNineFour12.region 0:=by decide +kernel
theorem square_shift:∀i,[186,187,212,213]⊆212::(locks i).erase 238:=by decide +kernel
theorem three_shift:∀i,(CageLedger12.Upper++[212,238]++Ring28812.locks 0)⊆212::(locks i).erase 213:=by decide +kernel
theorem bonus:RightEnergy12.cert.bonus 213 (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2:=by decide +kernel
#print axioms matrix
theorem energy_six {state final dirs pushes moves outcomes history past pastMoves}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (uniqueG:group.Nodup) (subset:group⊆state.boulders) (completed:Goal final)
 {i:Fin 2}(hero:state.player∈region i) (inside:locks i⊆group):6≤energy p group outcomes:=by
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group uniqueG subset hero inside with event|terminal
 ·obtain⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays⟩:=event.split
  have atReached:=reached.append first.trace
  have old:=first.end_subset actual group uniqueG subset
  have nextActual:=step_boulders_nodup _ _ _ _ (atReached.boulders_nodup (by decide +kernel)) checked
  have nextUnique:=GhostSubset.update_unique middle t outcome effect nextActual _ old.1 old.2
  have nextSubset:=GhostSubset.update_subset middle t outcome effect _ old.1 old.2
  have nextReached:=atReached.append (Trace.cons checked (Trace.nil t.state))
  have prefixNN:=first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0≤ownSlack p group before at prefixNN
  cases outcome with
  |walk target=>exact False.elim pays
  |push source ending=>
   obtain⟨owner,paidHead⟩:=pays
   have reserve (a b:Int) (one:a≤slack p (.push source ending))
    (later:b≤energy p (update (endGroup group before) (.push source ending)) after):
    a+b≤energy p group outcomes:=by
    rw[shape,energy_at_split]
    simp only[projectedOutcome,if_pos owner]
    omega
   rcases paidHead with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
      (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
    subst ending
    have kept:=CageFour12.shifted_inside (unique j) locksHead owner (h9_shift j)
    have heroNext:t.state.player∈PreAccessNineFour12.region 0:=by
      rw[matches_hero middle t (.push 263 (.stay 262)) effect];exact h9_hero
    have later:=PreAccessNineFour12.energy_four last nextReached _ nextUnique nextSubset completed heroNext kept
    change 4≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
    exact reserve 2 4 (by decide +kernel) later
   ·have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
      (show pushTargets soko1_2.board 213 .west=[212] by decide +kernel) (by decide +kernel) checked effect
    subst ending
    have kept:=CageFour12.shifted_inside (unique j) locksHead owner (three_shift j)
    have uInside:=List.Subset.trans (List.subset_append_left (CageLedger12.Upper++[212,238]) (Ring28812.locks 0)) kept
    have rInside:=List.Subset.trans (List.subset_append_right (CageLedger12.Upper++[212,238]) (Ring28812.locks 0)) kept
    have upInside:=List.Subset.trans (List.subset_append_left CageLedger12.Upper [212,238]) uInside
    have pairInside:=List.Subset.trans (List.subset_append_right CageLedger12.Upper [212,238]) uInside
    have u:=RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper (by decide +kernel)
      (List.Subset.trans upInside nextSubset) completed
    rw[matches_hero middle t (.push 213 (.stay 212)) effect] at u
    change RightEnergy12.cert.bonus 213 (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)≤energy p CageLedger12.Upper after at u
    rw[bonus] at u
    have vHero:t.state.player∈Vertical21223812.region 0:=by
      rw[matches_hero middle t (.push 213 (.stay 212)) effect];decide +kernel
    have v:=Vertical21223812.owned_energy_two last nextReached [212,238] (by decide +kernel)
      (List.Subset.trans pairInside nextSubset) vHero (fun _ h=>h)
    have rHero:t.state.player∈Ring28812.region 0:=by
      rw[matches_hero middle t (.push 213 (.stay 212)) effect];decide +kernel
    have r:=Ring28812.owned_energy_two last nextReached (Ring28812.locks 0) (Ring28812.unique 0)
      (List.Subset.trans rInside nextSubset) completed rHero (fun _ h=>h)
    change 2≤energy p CageLedger12.Upper after at u
    change 2≤energy p [212,238] after at v
    change 2≤energy p (Ring28812.locks 0) after at r
    have split:=last.energy_split nextActual p CageLedger12.Upper [212,238] (by decide +kernel) (List.Subset.trans uInside nextSubset)
    have add:=TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual
      (CageLedger12.Upper++[212,238]) (Ring28812.locks 0) (update (endGroup group before) (.push 213 (.stay 212)))
      (by decide +kernel) nextUnique nextSubset kept
    change energy p (CageLedger12.Upper++[212,238]) after+energy p (Ring28812.locks 0) after≤
      energy p (update (endGroup group before) (.push 213 (.stay 212))) after at add
    have later:6≤energy p (update (endGroup group before) (.push 213 (.stay 212))) after:=by omega
    have bound:=reserve 0 6 (by decide +kernel) later
    omega
   ·have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
      (show pushTargets soko1_2.board 238 .north=[212] by decide +kernel) (by decide +kernel) checked effect
    subst ending
    have kept:=CageFour12.shifted_inside (unique j) locksHead owner (square_shift j)
    have later:=last.locked_group_energy Generated.soko1_2_potential_valid nextActual _
      nextUnique nextSubset [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
    change debtOf p [186,187,212,213]≤energy p (update (endGroup group before) (.push 238 (.stay 212))) after at later
    have amount:(6:Int)≤debtOf p [186,187,212,213]:=by decide +kernel
    have one:=logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
    have bound:=reserve 0 (debtOf p [186,187,212,213]) one later
    omega
 ·obtain⟨j,_,kept⟩:=terminal
  have finalInside:=logged.end_subset actual group uniqueG subset
  have count:=List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept finalInside.2)
  rw[size j] at count
  have conserved:=(reached.append logged.trace).conservation
  have empty:final.holes=[]:=completed
  change 20+final.holes.length=final.boulders.length+18 at conserved
  rw[empty] at conserved
  simp only[List.length_nil] at conserved
  omega
#print axioms energy_six
end Owner1007.Deep288Six12
