import Owner1007.Post187Nine12
import Owner1007.FastCorral11
namespace Owner1007.Post187BareNine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def basic (i:Fin 4):Fin 6:=⟨i.val,by omega⟩
def oldIndex (i:Fin 6):Fin 10:=⟨i.val,by omega⟩
def locks (i:Fin 6):List Cell:=
 if i.val<4 then Post18712.upper++[212]++Post18712.core (oldIndex i)
 else if i.val=4 then [210,236] else [184,210]
def region (i:Fin 6):List Cell:=
 if h:i.val<4 then Cage10.region ⟨i.val+4,by omega⟩++[187]
 else soko1_2.board.floor.filter fun c=>!(locks i).contains c
abbrev paid:=Post18712.paid
theorem checked:∀i,FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid i=true:=by decide +kernel
theorem unique:∀i,(locks i).Nodup:=by decide +kernel
theorem floors:∀i,region i⊆soko1_2.board.floor:=by decide +kernel
theorem closed:PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid:=
 FastCorral11.closed_of_checks _ _ _ _ _ Post187Seven12.reverse floors checked
def classified (i:Fin 6) (source:Cell) (dir:Dir):Prop:=
 BlockedPush soko1_2.board (locks i) source dir∨
 (((source=186∧dir=.west)∨(source=211∧dir=.north))∧
  ([158,159,185,210]⊆185::(locks i).erase source∨[158,159,184,185]⊆185::(locks i).erase source))∨
 (source=212∧dir=.west∧[210,211,237,262]⊆211::(locks i).erase source)∨
 (source=238∧(dir=.east∨dir=.west))∨(source=262∧dir=.south)∨(source=161∧dir=.north)
instance (i:Fin 6)(source:Cell)(dir:Dir):Decidable (classified i source dir):=by unfold classified;infer_instance
def check (i:Fin 4):Bool:=
 Post18712.paidSources.all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region (basic i)∨source∉locks (basic i)∨¬paid source dir∨classified (basic i) source dir)
theorem rows:∀i,check i=true:=by decide +kernel
theorem classification (i:Fin 4)(hero:Cell)(heroInside:hero∈region (basic i))
 (dir:Dir)(source:Cell)(member:source∈Post18712.paidSources)
 (sourceK : source∈locks (basic i))
 (adjacent:advance soko1_2.board hero dir=some source)(paidHead:paid source dir):
 classified (basic i) source dir:=by
 have floor:=floors _ heroInside
 have behind:=Geometry.reverseCheck_sound soko1_2.board Post187Seven12.reverse hero floor dir source adjacent
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (rows i) source member) dir (Geometry.all_directions dir)
 simp only[check,behind]at row
 rcases of_decide_eq_true row with outside|outsideK|unpaid|okay
 ·exact False.elim (outside heroInside)
 ·exact False.elim (outsideK sourceK)
 ·exact False.elim (unpaid paidHead)
 ·exact okay
def postIndex (i:Fin 6):Fin 11:=if i.val<4 then ⟨i.val%4,by omega⟩ else if i.val=4 then 7 else 5
theorem post_inside:∀i,Post187Seven12.locks (postIndex i)⊆locks i:=by decide +kernel
theorem post_region:∀i,region i⊆Post187Seven12.region (postIndex i):=by decide +kernel
theorem post_credit:∀i,Post187Seven12.credit (postIndex i)=7:=by decide +kernel
theorem badPair:∀i:Fin 6,4≤i.val→[210,236]⊆locks i∨[184,210]⊆locks i:=by decide +kernel
theorem foreign_member {source : Cell} {dir : Dir}(h:source=238∧(dir=.east∨dir=.west)):source∈([238]:List Cell):=by obtain⟨rfl,_⟩:=h;decide +kernel
theorem foreign_price:∀source∈([238]:List Cell),∀dir∈allDirs,(source=238∧(dir=.east∨dir=.west))→
 ∀dest∈pushTargets soko1_2.board source dir,dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder source:=by decide +kernel
theorem foreign_hero:∀i:Fin 4,∀source∈([238]:List Cell),source∈Post187Seven12.region (postIndex (basic i)):=by decide +kernel
theorem upper_shift:∀i:Fin 4,UpperAfter18712.locks 0⊆288::(locks (basic i)).erase 262:=by decide +kernel
theorem upper_hero:(262:Cell)∈UpperAfter18712.region 0:=by decide +kernel
theorem pair_shift:∀i:Fin 4,VerticalPair12.pair false⊆135::(locks (basic i)).erase 161:=by decide +kernel
theorem pair_hero:(161:Cell)∈VerticalPair12.region false 0:=by decide +kernel
theorem normal_size:∀i:Fin 6,i.val<4→(locks i).length=10:=by decide +kernel
theorem max_size:∀i:Fin 6,(locks i).length≤10:=by decide +kernel
theorem terminal_debt:∀i:Fin 6,(9:Int)≤debtOf p (locks i):=by decide +kernel
#print axioms checked
#print axioms rows
end Owner1007.Post187BareNine12

namespace Owner1007.Post187BareNine12
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
 (i : Fin 6) (bad : 4≤i.val) (inside : Post187BareNine12.locks i⊆group) :
 9≤energy p group outcomes :=by
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases Post187BareNine12.badPair i bad with a|b
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
theorem core_nine {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (i : Fin 6) (hero : state.player∈Post187BareNine12.region i)
 (subset : Post187BareNine12.locks i⊆state.boulders) :
 9≤energy p (Post187BareNine12.locks i) outcomes :=by
 let group:=Post187BareNine12.locks i
 have gUnique:=Post187BareNine12.unique i
 change 9≤energy p group outcomes
 have closed:=Post187BareNine12.closed
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed Post187BareNine12.unique logged reached group gUnique subset hero (fun _ h=>h) with event|terminal
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
  by_cases normal:j.val<4
  ·let k:Fin 4:=⟨j.val,normal⟩
   have same:Post187BareNine12.basic k=j:=Fin.ext rfl
   cases outcome with
   |walk target=>exact False.elim pays
   |push source ending=>
    obtain ⟨owner,paid⟩:=pays
    obtain ⟨_,adjacent,_⟩:=effect_push_data checked effect
    have member : source∈Post187BareNine12.locks j := by
      apply Classical.byContradiction
      intro absent
      have together: source::Post187BareNine12.locks j⊆endGroup group before:=
        List.cons_subset.mpr ⟨owner,locksHead⟩
      have count:=List.Nodup.length_le_of_subset
        (List.nodup_cons.mpr ⟨absent,Post187BareNine12.unique j⟩) together
      have size:=Post187BareNine12.normal_size j normal
      have short:=endGroup_length_le group before
      have max:=Post187BareNine12.max_size i
      change group.length≤10 at max
      simp only[List.length_cons] at count
      omega
    have sharper:=classification k middle.player (by simpa only[same] using heroHead) dir source
      (Post18712.paid_sources source dir paid) (by simpa only[same] using member) adjacent paid
    rw[same] at sharper
    have headNN:=logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
    change 0≤slack p (.push source ending) at headNN
    have whole:energy p group outcomes=ownSlack p group before+slack p (.push source ending)+
      energy p (update (endGroup group before) (.push source ending)) after:=by
      rw[shape,energy_at_split]
      simp only[projectedOutcome,if_pos owner]
    rcases sharper with blocked|gate|quad|ticket|south|upper
    ·exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksHead old.2) checked effect blocked)
    ·have targets:pushTargets soko1_2.board source dir=[185]:=by
       rcases gate.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>decide +kernel
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset targets
       (by decide +kernel) checked effect
     subst ending
     rcases gate.2 with g|square
     ·have kept:=CageFour12.shifted_inside (Post187BareNine12.unique j) locksHead owner g
      have heroNext:t.state.player∈PriceTrap12Gate.region 0:=by
        rw[matches_hero middle t (.push source (.stay 185)) effect]
        rcases gate.1 with ⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
      have later:=CageLedger12.gate_owned_nineteen last nextReached _ nextUnique nextSubset heroNext kept
      change 19≤energy p (update (endGroup group before) (.push source (.stay 185))) after at later
      omega
     ·have kept:=CageFour12.shifted_inside (Post187BareNine12.unique j) locksHead owner square
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
     have kept:=CageFour12.shifted_inside (Post187BareNine12.unique j) locksHead owner shift
     have heroNext:t.state.player∈Quad211Trap12.region 0:=by
       rw[matches_hero middle t (.push 212 (.stay 211)) effect]
       decide +kernel
     have later:=Quad211Trap12.owned_energy_fifteen last nextReached _ nextUnique nextSubset heroNext kept
     change 15≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
     omega
    ·have member:=foreign_member ticket
     have price:=push_effect_price p soko1_2.initial.holes 2 atReached.holes_sublist.subset
       (foreign_price source member dir (Geometry.all_directions dir) ticket) checked effect
     have beforeSeven:=List.Subset.trans (post_inside j) locksHead
     have absent:source∉Post187Seven12.locks (postIndex j):=by
       have finite:∀i:Fin 6,∀c∈([238]:List Cell),c∉Post187Seven12.locks (postIndex i):=by decide +kernel
       exact finite j source member
     have keep:=update_mono (Post187Seven12.locks (postIndex j))
       (endGroup group before) (Post187Seven12.unique _) beforeSeven (.push source ending)
     have unchanged:update (Post187Seven12.locks (postIndex j)) (.push source ending)=
       Post187Seven12.locks (postIndex j):=by simp only[update,move,if_neg absent]
     rw[unchanged] at keep
     have heroNext:t.state.player∈Post187Seven12.region (postIndex j):=by
       rw[matches_hero middle t (.push source ending) effect]
       simpa only[same,nextHero] using foreign_hero k source member
     have later:=Post187Seven12.owned_energy_seven last nextReached _ nextUnique nextSubset
       (post_credit j) heroNext keep
     change 7≤energy p (update (endGroup group before) (.push source ending)) after at later
     omega
    ·obtain ⟨rfl,rfl⟩:=south
     have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 262 .south=[288] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     have shift:UpperAfter18712.locks 0⊆288::(Post187BareNine12.locks j).erase 262:=by simpa only[same] using upper_shift k
     have kept:=CageFour12.shifted_inside (Post187BareNine12.unique j) locksHead owner shift
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
     have shift:VerticalPair12.pair false⊆135::(Post187BareNine12.locks j).erase 161:=by simpa only[same] using pair_shift k
     have kept:=CageFour12.shifted_inside (Post187BareNine12.unique j) locksHead owner shift
     have heroNext:t.state.player∈VerticalPair12.region false 0:=by
       rw[matches_hero middle t (.push 161 (.stay 135)) effect]
       exact pair_hero
     have later:=VerticalPair12.owned_energy_two false last nextReached _ nextUnique nextSubset heroNext kept
     change 2≤energy p (update (endGroup group before) (.push 161 (.stay 135))) after at later
     have one:slack p (.push 161 (.stay 135))=8:=by decide +kernel
     rw[one] at whole
     omega
  ·have full:=Logged.cons checked effect last
   have later:=bad_nine full atReached (endGroup group before) old.1 old.2 j (by omega) locksHead
   have expanded:=TokenAccounting.energy_append p group before (outcome::after)
   rw[←shape] at expanded
   omega
 ·obtain ⟨j,_,kept⟩:=terminal
  have debt:=NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
    (Post187BareNine12.locks j) (endGroup group outcomes)
    (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
    (Post187BareNine12.unique j) kept
  change debtOf p (Post187BareNine12.locks j)≤debtOf p (endGroup group outcomes) at debt
  have nine:=terminal_debt j
  have nn:=logged.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0≤ownSlack p group outcomes at nn
  unfold energy
  omega

theorem energy_nine {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 6} (hero : state.player∈region i) (inside : locks i⊆group):
 9≤energy p group outcomes:=by
 have actual:=reached.boulders_nodup (by decide +kernel)
 have smallActual:=List.Subset.trans inside subset
 have bound:=core_nine logged reached i hero smallActual
 have mono:=logged.energy_mono Generated.soko1_2_potential_valid actual
   (locks i) group (unique i) gUnique smallActual subset inside
 change energy p (locks i) outcomes≤energy p group outcomes at mono
 omega
#print axioms core_nine
#print axioms energy_nine
end Owner1007.Post187BareNine12
