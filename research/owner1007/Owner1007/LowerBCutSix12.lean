import Owner1007.LowerBCut12
import Owner1007.BottomAny12
import Owner1007.After265PureSeven12
import Owner1007.ResidualBoost12
import Owner1007.SurvivorPrefix12
import Owner1007.Post187Seven12
namespace Owner1007.LowerBCutSix12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.LowerBCut12 (C B locks region paid)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def bottomIndex (i:Fin 5):Fin 11:=⟨i.val+1,by omega⟩
theorem bottom_shift:∀i,∀c∈([263,264]:List Cell),
 BottomCut12.locks (bottomIndex i)⊆(c+26)::(locks i).erase c:=by decide +kernel
theorem bottom_hero:∀i,∀c∈([263,264]:List Cell),c∈BottomCut12.region (bottomIndex i):=by decide +kernel
theorem bottom_credit:∀i,BottomCut12.credit (bottomIndex i)=2:=by decide +kernel
theorem targets_four:∀c∈([263,264]:List Cell),pushTargets soko1_2.board c .south=[c+26] ∧
 c+26∉soko1_2.initial.holes ∧slack p (.push c (.stay (c+26)))=4:=by decide +kernel
theorem after265_shift:∀(i:Fin 5)(j:Fin 4),i.val=j.val→
 After26512.locks j⊆291::(locks i).erase 265:=by decide +kernel
theorem park_constraints:∀i,(319:Cell)∈region i→
 NorthEvents12.current i∈DeadCorridor12.corridor ∧(4:Int)≤-p.boulder (NorthEvents12.current i):=by decide +kernel
theorem park_shift:∀i,([NorthEvents12.current i]:List Cell)⊆317::(locks i).erase 318:=by decide +kernel
theorem ring_shift:∀i,ResidualBoost12.locks 1⊆290::(locks i).erase 291:=by decide +kernel

theorem energy_six {state final dirs pushes moves outcomes}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir} {past pastMoves:Nat}
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (gUnique:group.Nodup) (subset:group⊆state.boulders)
 (completed:Goal final) {i:Fin 5} (hero:state.player∈region i) (inside:locks i⊆group):
 6≤energy p group outcomes:=by
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ LowerBCut12.matrix
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed LowerBCut12.unique logged reached group gUnique subset hero inside with event|terminal
 ·obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays⟩:=event.split
  have atReached:=reached.append first.trace
  have atActual:=atReached.boulders_nodup (by decide +kernel)
  have old:=first.end_subset actual group gUnique subset
  have nextActual:=step_boulders_nodup _ _ _ _ atActual checked
  have nextUnique:=GhostSubset.update_unique middle t outcome effect nextActual _ old.1 old.2
  have nextSubset:=GhostSubset.update_subset middle t outcome effect _ old.1 old.2
  have nextReached:=atReached.append (Trace.cons checked (Trace.nil t.state))
  have prefixNN:=first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0≤ownSlack p group before at prefixNN
  cases outcome with
  |walk target=>exact False.elim pays
  |push source ending=>
   obtain ⟨owner,headPaid⟩:=pays
   have reserve (a b:Int) (one:a≤slack p (.push source ending))
    (later:b≤energy p (update (endGroup group before) (.push source ending)) after):
    a+b≤energy p group outcomes:=by
    rw[shape,energy_at_split]
    simp only[projectedOutcome,if_pos owner]
    omega
   rcases headPaid with ⟨core,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·have four_head (member:source∈([263,264]:List Cell)):6≤energy p group outcomes:=by
      obtain ⟨targets,clear,price⟩:=targets_four source member
      have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset targets clear checked effect
      subst ending
      have kept:=CageFour12.shifted_inside (LowerBCut12.unique j) locksHead owner (bottom_shift j source member)
      have heroNext:t.state.player∈BottomCut12.region (bottomIndex j):=by
       rw[matches_hero middle t (.push source (.stay (source+26))) effect]
       exact bottom_hero j source member
      have later:=BottomAny12.owned_credit last nextReached _ nextUnique nextSubset heroNext kept
      rw[bottom_credit] at later
      change 2≤energy p (update (endGroup group before) (.push source (.stay (source+26)))) after at later
      have bound:=reserve 4 2 (by rw[price]; omega) later
      omega
    have choices:source=262∨source=263∨source=264∨source=265:=by
     simpa only[C,List.mem_cons,List.not_mem_nil,or_false] using core
    rcases choices with rfl|rfl|rfl|rfl
    ·have price:=push_effect_price p soko1_2.initial.holes 7 atReached.holes_sublist.subset
       (show ∀dest∈pushTargets soko1_2.board 262 .south,
        dest∉soko1_2.initial.holes∧(7:Int)≤1+p.boulder dest-p.boulder 262 from by decide +kernel) checked effect
     have later:=last.energy_nonnegative Generated.soko1_2_potential_valid (update (endGroup group before) (.push 262 ending))
     change 0≤energy p (update (endGroup group before) (.push 262 ending)) after at later
     have bound:=reserve 7 0 price later
     omega
    ·exact four_head (by decide +kernel)
    ·exact four_head (by decide +kernel)
    ·have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     obtain ⟨result,_,push⟩:=effect_push_data checked effect
     obtain ⟨dest,next,_,_,empty⟩:=(push_first_clear soko1_2.board middle 265 .south result push).2
     have destEq:dest=291:=Option.some.inj (next.symm.trans (by decide +kernel))
     have clear291:291∉middle.boulders:=by simpa only[destEq] using empty
     have physical:=List.Subset.trans locksHead old.2
     have small:j.val<4:=by
      by_cases yes:j.val<4
      ·exact yes
      ·have v:j.val=4:=by have h:=j.isLt;omega
       have same:j=(4:Fin 5):=Fin.ext v
       subst j
       exact False.elim (clear291 (physical (by decide +kernel)))
     let k:Fin 4:=⟨j.val,small⟩
     have kept:=CageFour12.shifted_inside (LowerBCut12.unique j) locksHead owner (after265_shift j k rfl)
     have heroNext:t.state.player∈After26512.region k:=by
      rw[matches_hero middle t (.push 265 (.stay 291)) effect]
      exact After26512.start_hero k
     have later:=After265PureSeven12.energy_seven last nextReached _ nextUnique nextSubset completed heroNext kept
     change 7≤energy p (update (endGroup group before) (.push 265 (.stay 291))) after at later
     have bound:=reserve 2 7 (by decide +kernel) later
     omega
   ·have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
      (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel) (by decide +kernel) checked effect
    subst ending
    obtain ⟨_,adjacent,_⟩:=effect_push_data checked effect
    have floor:middle.player∈soko1_2.board.floor:=(step_player_clear _ _ _ _ checked).1
    have reverse:=Geometry.reverseCheck_sound soko1_2.board Post187Seven12.reverse middle.player floor .west 318 adjacent
    have heroEq:middle.player=319:=Option.some.inj (reverse.symm.trans (by decide +kernel))
    have constraints:=park_constraints j (by simpa only[heroEq] using heroHead)
    have shapeNext:t.state.boulders=317::middle.boulders.erase 318:=by
     simpa only[Matches] using congrArg (fun z:Transition=>z.state.boulders) effect.2
    have present:317∈t.state.boulders:=by rw[shapeNext];simp
    have alive:=DeadCorridor12.trapped_survives last present nextReached.holes_sublist.subset
      (NorthEvents12.current j) constraints.1
    have ledger:=survivor_energy p (NorthEvents12.current j) after alive
    have countNN:(0:Int)≤Int.ofNat (ownPushes [NorthEvents12.current j] after):=Int.natCast_nonneg _
    have single:4≤energy p [NorthEvents12.current j] after:=by omega
    have kept:=CageFour12.shifted_inside (LowerBCut12.unique j) locksHead owner (park_shift j)
    have singlePhysical:=List.Subset.trans kept nextSubset
    have mono:=last.energy_mono Generated.soko1_2_potential_valid nextActual [NorthEvents12.current j]
      (update (endGroup group before) (.push 318 (.stay 317))) (by simp) nextUnique singlePhysical nextSubset kept
    change energy p [NorthEvents12.current j] after≤energy p (update (endGroup group before) (.push 318 (.stay 317))) after at mono
    have later:4≤energy p (update (endGroup group before) (.push 318 (.stay 317))) after:=by omega
    have bound:=reserve 3 4 (by decide +kernel) later
    omega
   ·have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
      NorthEvents12.ring_activation (by decide +kernel) checked effect
    subst ending
    have kept:=CageFour12.shifted_inside (LowerBCut12.unique j) locksHead owner (ring_shift j)
    have heroNext:t.state.player∈ResidualBoost12.region 1:=by
     rw[matches_hero middle t (.push 291 (.stay 290)) effect]
     decide +kernel
    have later:=ResidualBoost12.owned_credit last nextReached _ nextUnique nextSubset 1 heroNext kept
    change 7≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after at later
    have bound:=reserve 2 7 (by decide +kernel) later
    omega
 ·obtain ⟨j,_,kept⟩:=terminal
  have finalInside:=logged.end_subset actual group gUnique subset
  have count:=List.Nodup.length_le_of_subset (LowerBCut12.unique j) (List.Subset.trans kept finalInside.2)
  rw[LowerBCut12.large] at count
  have conserved:=(reached.append logged.trace).conservation
  have empty:final.holes=[]:=completed
  change 20+final.holes.length=final.boulders.length+18 at conserved
  rw[empty] at conserved
  simp only[List.length_nil] at conserved
  omega
#print axioms energy_six
end Owner1007.LowerBCutSix12
