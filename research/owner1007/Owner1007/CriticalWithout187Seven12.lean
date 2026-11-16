import Owner1007.CriticalWithout18712Data
import Owner1007.After265PureEight12
import Owner1007.ResidualBoost12
import Owner1007.Quad211Trap12
import Owner1007.SurvivorPrefix12
import Owner1007.Post187Seven12
namespace Owner1007.CriticalWithout187Seven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.CriticalWithout18712 (Core locks region paid)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def sharp (i:Fin 5) (source:Cell) (dir:Dir):Bool:=
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_2.board (locks i) source dir∨
 ((source=210∧dir=.south)∨(source=237∧dir=.west)∨(source=263∧dir=.west)∨(source=265∧dir=.south)))
theorem sharp_rows:∀i,∀source∈Core,∀dir∈allDirs,sharp i source dir=true:=by decide +kernel
theorem first_shift:∀i,ResidualBoost12.locks 0⊆236::(locks i).erase 210:=by decide +kernel
theorem locked_shift:∀i,[210,236]⊆236::(locks i).erase 237:=by decide +kernel
theorem quad_shift:∀i,Quad211Trap12.locks 0⊆262::(locks i).erase 263:=by decide +kernel
theorem after265_shift:∀(i:Fin 5) (j:Fin 4),i.val=j.val→After26512.locks j⊆291::(locks i).erase 265:=by decide +kernel
theorem park_constraints:∀i,(319:Cell)∈region i→NorthEvents12.current i∈DeadCorridor12.corridor∧(4:Int)≤-p.boulder (NorthEvents12.current i):=by decide +kernel
theorem park_shift:∀i,[NorthEvents12.current i]⊆317::(locks i).erase 318:=by decide +kernel
theorem energy_seven {state final dirs pushes moves outcomes}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir} {past pastMoves:Nat}
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (gUnique:group.Nodup) (subset:group⊆state.boulders)
 (completed:Goal final) {i:Fin 5} (hero:state.player∈region i) (inside:locks i⊆group):
 7≤energy p group outcomes:=by
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ CriticalWithout18712.matrix
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed CriticalWithout18712.unique logged reached group gUnique subset hero inside with event|terminal
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
   rcases headPaid with core|⟨rfl,rfl⟩
   ·obtain⟨_,adjacent,_⟩:=effect_push_data checked effect
    have floor:middle.player∈soko1_2.board.floor:=(step_player_clear _ _ _ _ checked).1
    have back:=Geometry.reverseCheck_sound soko1_2.board Post187Seven12.reverse middle.player floor dir source adjacent
    have row:=sharp_rows j source core dir (Geometry.all_directions dir)
    simp only[sharp,back] at row
    rcases of_decide_eq_true row with outside|blocked|h210|h237|h263|h265
    ·exact False.elim (outside heroHead)
    ·exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksHead old.2) checked effect blocked)
    ·obtain⟨rfl,rfl⟩:=h210
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have kept:=CageFour12.shifted_inside (CriticalWithout18712.unique j) locksHead owner (first_shift j)
     have heroNext:t.state.player∈ResidualBoost12.region 0:=by
       rw[matches_hero middle t (.push 210 (.stay 236)) effect];decide +kernel
     have later:=ResidualBoost12.owned_credit last nextReached _ nextUnique nextSubset 0 heroNext kept
     change 7≤energy p (update (endGroup group before) (.push 210 (.stay 236))) after at later
     have bound:=reserve 2 7 (by decide +kernel) later
     omega
    ·obtain⟨rfl,rfl⟩:=h237
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 237 .west=[236] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have kept:=CageFour12.shifted_inside (CriticalWithout18712.unique j) locksHead owner (locked_shift j)
     have later:=last.locked_group_energy Generated.soko1_2_potential_valid nextActual _
       nextUnique nextSubset [210,236] CageLedger12.locked_210236 (by decide +kernel) kept
     change debtOf p [210,236]≤energy p (update (endGroup group before) (.push 237 (.stay 236))) after at later
     have amount:(7:Int)≤debtOf p [210,236]:=by decide +kernel
     have bound:=reserve 2 (debtOf p [210,236]) (by decide +kernel) later
     omega
    ·obtain⟨rfl,rfl⟩:=h263
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have kept:=CageFour12.shifted_inside (CriticalWithout18712.unique j) locksHead owner (quad_shift j)
     have heroNext:t.state.player∈Quad211Trap12.region 0:=by
       rw[matches_hero middle t (.push 263 (.stay 262)) effect];decide +kernel
     have later:=Quad211Trap12.owned_energy_fifteen last nextReached _ nextUnique nextSubset heroNext kept
     change 15≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
     have bound:=reserve 2 15 (by decide +kernel) later
     omega
    ·obtain⟨rfl,rfl⟩:=h265
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
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
     have kept:=CageFour12.shifted_inside (CriticalWithout18712.unique j) locksHead owner (after265_shift j k rfl)
     have heroNext:t.state.player∈After26512.region k:=by
      rw[matches_hero middle t (.push 265 (.stay 291)) effect]
      exact After26512.start_hero k
     have later:=After265PureEight12.energy_eight last nextReached _ nextUnique nextSubset completed heroNext kept
     change 8≤energy p (update (endGroup group before) (.push 265 (.stay 291))) after at later
     have bound:=reserve 2 8 (by decide +kernel) later
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
    have kept:=CageFour12.shifted_inside (CriticalWithout18712.unique j) locksHead owner (park_shift j)
    have singlePhysical:=List.Subset.trans kept nextSubset
    have mono:=last.energy_mono Generated.soko1_2_potential_valid nextActual [NorthEvents12.current j]
      (update (endGroup group before) (.push 318 (.stay 317))) (by simp) nextUnique singlePhysical nextSubset kept
    change energy p [NorthEvents12.current j] after≤energy p (update (endGroup group before) (.push 318 (.stay 317))) after at mono
    have later:4≤energy p (update (endGroup group before) (.push 318 (.stay 317))) after:=by omega
    have bound:=reserve 3 4 (by decide +kernel) later
    omega
 ·obtain ⟨j,_,kept⟩:=terminal
  have finalInside:=logged.end_subset actual group gUnique subset
  have count:=List.Nodup.length_le_of_subset (CriticalWithout18712.unique j) (List.Subset.trans kept finalInside.2)
  rw[CriticalWithout18712.size] at count
  have conserved:=(reached.append logged.trace).conservation
  have empty:final.holes=[]:=completed
  change 20+final.holes.length=final.boulders.length+18 at conserved
  rw[empty] at conserved
  simp only[List.length_nil] at conserved
  omega
#print axioms energy_seven
end Owner1007.CriticalWithout187Seven12
