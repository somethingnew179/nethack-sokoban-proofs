import Owner1007.Post187Nine12Data
import Owner1007.Quad211Trap12
namespace Owner1007.Post187Nine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem bad_nine {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 10) (bad : 8≤i.val) (inside : Post18712.locks i⊆group) :
 9≤energy p group outcomes :=by
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases Post18712.badPair i bad with a|b
 ·have bound:=logged.locked_group_energy Generated.soko1_2_potential_valid actual group gUnique subset
    [210,236] CageLedger12.locked_210236 (by decide +kernel) (List.Subset.trans a inside)
  have amount:(9:Int)≤debtOf p [210,236]:=by decide +kernel
  change debtOf p [210,236]≤energy p group outcomes at bound
  omega
 ·have bound:=logged.locked_group_energy Generated.soko1_2_potential_valid actual group gUnique subset
    [184,210] CageLedger12.locked_184210 (by decide +kernel) (List.Subset.trans b inside)
  have amount:(9:Int)≤debtOf p [184,210]:=by decide +kernel
  change debtOf p [184,210]≤energy p group outcomes at bound
  omega

/-- Nine owned units for all actual suffixes, including partial ones.
The old phase and walking certificate is unchanged. -/
theorem energy_nine {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 10} (hero : state.player∈Post18712.region i) (inside : Post18712.locks i⊆group) :
 9≤energy p group outcomes :=by
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ Post18712.matrix
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed Post18712.unique logged reached group gUnique subset hero inside with event|terminal
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
  by_cases normal:j.val<8
  ·let k:Fin 8:=⟨j.val,normal⟩
   have same:Post18712.basic k=j:=Fin.ext rfl
   cases outcome with
   |walk target=>exact False.elim pays
   |push source ending=>
    obtain ⟨owner,paid⟩:=pays
    obtain ⟨_,adjacent,_⟩:=effect_push_data checked effect
    have sharper:=classification k middle.player (by simpa only[same] using heroHead) dir source
      (Post18712.paid_sources source dir paid) adjacent paid
    rw[same] at sharper
    have headNN:=logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
    change 0≤slack p (.push source ending) at headNN
    have whole:energy p group outcomes=ownSlack p group before+slack p (.push source ending)+
      energy p (update (endGroup group before) (.push source ending)) after:=by
      rw[shape,energy_at_split]
      simp only[projectedOutcome,if_pos owner]
    rcases sharper with blocked|gate|quad|ticket|south|upper|dead
    ·exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksHead old.2) checked effect blocked)
    ·have targets:pushTargets soko1_2.board source dir=[185]:=by
       rcases gate.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>decide +kernel
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset targets
       (by decide +kernel) checked effect
     subst ending
     rcases gate.2 with g|square
     ·have kept:=CageFour12.shifted_inside (Post18712.unique j) locksHead owner g
      have heroNext:t.state.player∈PriceTrap12Gate.region 0:=by
        rw[matches_hero middle t (.push source (.stay 185)) effect]
        rcases gate.1 with ⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
      have later:=CageLedger12.gate_owned_nineteen last nextReached _ nextUnique nextSubset heroNext kept
      change 19≤energy p (update (endGroup group before) (.push source (.stay 185))) after at later
      omega
     ·have kept:=CageFour12.shifted_inside (Post18712.unique j) locksHead owner square
      have later:=last.locked_group_energy Generated.soko1_2_potential_valid nextActual
        (update (endGroup group before) (.push source (.stay 185))) nextUnique nextSubset
        [158,159,184,185] CageLedger12.locked_upper_square (by decide +kernel) kept
      have amount:(9:Int)≤debtOf p [158,159,184,185]:=by decide +kernel
      change debtOf p [158,159,184,185]≤energy p (update (endGroup group before) (.push source (.stay 185))) after at later
      omega
    ·obtain ⟨rfl,rfl,shift⟩:=quad
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have kept:=CageFour12.shifted_inside (Post18712.unique j) locksHead owner shift
     have heroNext:t.state.player∈Quad211Trap12.region 0:=by
       rw[matches_hero middle t (.push 212 (.stay 211)) effect]
       decide +kernel
     have later:=Quad211Trap12.owned_energy_fifteen last nextReached _ nextUnique nextSubset heroNext kept
     change 15≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
     omega
    ·have member:=foreign_member ticket
     have price:=push_effect_price p soko1_2.initial.holes 2 atReached.holes_sublist.subset
       (foreign_price source member dir (Geometry.all_directions dir) ticket) checked effect
     have beforeSeven:=List.Subset.trans (Post187SevenMap12.post_inside j) locksHead
     have absent:source∉Post187Seven12.locks (Post187SevenMap12.postIndex j):=by
       have finite:∀i:Fin 10,∀c∈([239,238,213]:List Cell),c∉Post187Seven12.locks (Post187SevenMap12.postIndex i):=by decide +kernel
       exact finite j source member
     have keep:=update_mono (Post187Seven12.locks (Post187SevenMap12.postIndex j))
       (endGroup group before) (Post187Seven12.unique _) beforeSeven (.push source ending)
     have unchanged:update (Post187Seven12.locks (Post187SevenMap12.postIndex j)) (.push source ending)=
       Post187Seven12.locks (Post187SevenMap12.postIndex j):=by simp only[update,move,if_neg absent]
     rw[unchanged] at keep
     have heroNext:t.state.player∈Post187Seven12.region (Post187SevenMap12.postIndex j):=by
       rw[matches_hero middle t (.push source ending) effect]
       simpa only[same,nextHero] using foreign_hero k source member
     have later:=Post187Seven12.owned_energy_seven last nextReached _ nextUnique nextSubset
       (Post187SevenMap12.post_credit j) heroNext keep
     change 7≤energy p (update (endGroup group before) (.push source ending)) after at later
     omega
    ·obtain ⟨rfl,rfl⟩:=south
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 262 .south=[288] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have shift:UpperAfter18712.locks 0⊆288::(Post18712.locks j).erase 262:=by simpa only[same] using upper_shift k
     have kept:=CageFour12.shifted_inside (Post18712.unique j) locksHead owner shift
     have heroNext:t.state.player∈UpperAfter18712.region 0:=by
       rw[matches_hero middle t (.push 262 (.stay 288)) effect]
       exact upper_hero
     have later:=UpperAfter18712.owned_energy_two UpperAfter18712.matrix last nextReached _ nextUnique nextSubset heroNext kept
     change 2≤energy p (update (endGroup group before) (.push 262 (.stay 288))) after at later
     have one:slack p (.push 262 (.stay 288))=7:=by decide +kernel
     rw[one] at whole
     omega
    ·obtain ⟨rfl,rfl⟩:=upper
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 161 .north=[135] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have shift:VerticalPair12.pair false⊆135::(Post18712.locks j).erase 161:=by simpa only[same] using pair_shift k
     have kept:=CageFour12.shifted_inside (Post18712.unique j) locksHead owner shift
     have heroNext:t.state.player∈VerticalPair12.region false 0:=by
       rw[matches_hero middle t (.push 161 (.stay 135)) effect]
       exact pair_hero
     have later:=VerticalPair12.owned_energy_two false last nextReached _ nextUnique nextSubset heroNext kept
     change 2≤energy p (update (endGroup group before) (.push 161 (.stay 135))) after at later
     have one:slack p (.push 161 (.stay 135))=8:=by decide +kernel
     rw[one] at whole
     omega
    ·obtain ⟨rfl,rfl⟩:=dead
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 213 .north=[187] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have shift:([161,187]:List Cell)⊆187::(Post18712.locks j).erase 213:=by simpa only[same] using dead_shift k
     have kept:=CageFour12.shifted_inside (Post18712.unique j) locksHead owner shift
     have later:=last.locked_group_energy Generated.soko1_2_potential_valid nextActual
       (update (endGroup group before) (.push 213 (.stay 187))) nextUnique nextSubset
       [161,187] locked161187 (by decide +kernel) kept
     have amount:(9:Int)≤debtOf p [161,187]:=by decide +kernel
     change debtOf p [161,187]≤energy p (update (endGroup group before) (.push 213 (.stay 187))) after at later
     omega
  ·have full:=Logged.cons checked effect last
   have later:=bad_nine full atReached (endGroup group before) old.1 old.2 j (by omega) locksHead
   have expanded:=TokenAccounting.energy_append p group before (outcome::after)
   rw[←shape] at expanded
   omega
 ·obtain ⟨j,_,kept⟩:=terminal
  have debt:=NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
    (Post18712.locks j) (endGroup group outcomes)
    (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
    (Post18712.unique j) kept
  change debtOf p (Post18712.locks j)≤debtOf p (endGroup group outcomes) at debt
  have nine:=terminal_debt j
  have nn:=logged.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0≤ownSlack p group outcomes at nn
  unfold energy
  omega
#print axioms energy_nine
end Owner1007.Post187Nine12
