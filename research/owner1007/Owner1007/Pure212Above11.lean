import Owner1007.Upper216Eight11
import Owner1007.QuietFixed11
import Owner1007.Gate265Transport11Data
import Owner1007.PaidCount11
import Owner1007.RankedCorral11
import Owner1007.FirstRest18711
import Owner1007.UpperLocalPrice11
namespace Owner1007.Pure212Above11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def front (i : Fin 2) : Cell:=if i.val=0 then 213 else 239
def locks (i : Fin 2) : List Cell:=[front i]
def region (i : Fin 2) : List Cell := Gate265Transport11.upper.filter fun c=>
 !(if i.val=0 then ([213,239]:List Cell) else [239]).contains c

def paid (source : Cell) (dir : Dir) : Prop:=(source=213∧(dir=.east∨dir=.west))∨(source=239∧dir=.south)
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor:=by
 have row : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem size : ∀i,(locks i).length=1:=by decide +kernel
theorem front_inside : ∀i,front i∈locks i:=by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1:=by omega
 rcases cases with rfl|rfl
 · exact node0
 · exact node1

def refinementCheck (i : Fin 2) : Bool:=(locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>if hero∈region i then (List.finRange 2).all fun j=>
   (pushTargets soko1_1.board source dir).all fun dest=>decide
    (dir.diagonal=false→¬paid source dir→pushTargets soko1_1.board source dir=[dest]→
     dest∉soko1_1.initial.holes→locks j⊆dest::(locks i).erase source→source∈region j→
     update [front i] (.push source (.stay dest))=[front j])
   else true
theorem refinements : ∀i,refinementCheck i=true:=by decide +kernel
theorem refined : RankedCorral11.Refinement locks region front (fun _=>0) paid:=by
 intro i hero source dest dir j heroInside sourceInside adjacent cardinal unpaid target targets noHole nextLocks nextHero
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (refinements i) source sourceInside) dir (Geometry.all_directions dir)
 have reverse:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i heroInside) dir source adjacent
 simp only [refinementCheck,reverse,if_pos heroInside] at row
 have numeric:=List.all_eq_true.mp (List.all_eq_true.mp row j (by simp)) dest target
 exact ⟨of_decide_eq_true numeric cardinal unpaid targets noHole nextLocks nextHero,Or.inl (show (0:Int)≤0 from Int.le_refl _)⟩

theorem quiet_frame {state final group dirs pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤1)
 (i : Fin 2) (hero : state.player∈region i) (selected : locks i⊆group)
 (holes : state.holes⊆soko1_1.initial.holes) :
 ∃j : Fin 2, final.player∈region j ∧ locks j⊆endGroup group outcomes ∧ endGroup [front i] outcomes=[front j]:=by
 obtain ⟨j,lastHero,lastLocks,lastTag,_⟩:=RankedCorral11.quiet_rank closed unique size front_inside refined quiet valid groupUnique inside bounded i hero selected holes
 exact ⟨j,lastHero,lastLocks,lastTag⟩

theorem quiet_no_north {state final group dirs pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤1)
 (i : Fin 2) (hero : state.player∈region i) (selected : locks i⊆group)
 (holes : state.holes⊆soko1_1.initial.holes) :
 PaidCount11.count FirstRest18711.paid [front i] dirs outcomes=0:=by
 induction quiet generalizing i with
 |nil=>rfl
 |@cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih=>
   have headNotPaid : ¬PaidCount11.owned FirstRest18711.paid [front i] dir outcome:=by
     intro pays
     obtain ⟨source,owner,metadata,same,north⟩:=(PaidCount11.owned_iff effect).mp pays
     have sourceFront : source=front i:=List.mem_singleton.mp owner
     have frontEq : front i=213:=sourceFront.symm.trans same
     have adjacent:=PairPost11.source_adjacent checked metadata
     have heroEq:=ActorPrices11.support_of_check 213 state.player .north 239 (by decide +kernel)
       (step_player_clear _ _ _ _ checked).1 (by simpa only [same,north] using adjacent)
     have row : (List.finRange 2).all (fun i=>decide (front i=213→239∉region i))=true:=by decide +kernel
     have forbidden:=of_decide_eq_true (List.all_eq_true.mp row i (by simp)) frontEq
     exact forbidden (heroEq ▸ hero)
   obtain ⟨j,nextHero,nextLocks,nextMarker,_⟩:=RankedCorral11.step_rank closed unique size front_inside refined
     valid groupUnique i hero selected inside bounded holes checked effect avoid
   have nextValid:=(groupCertificate 1).preserved _ _ _ valid checked
   have nextActual:=step_boulders_nodup _ _ _ _ valid.1 checked
   have nextUnique:=GhostSubset.update_unique _ _ _ effect nextActual _ groupUnique inside
   have nextInside:=GhostSubset.update_subset _ _ _ effect _ groupUnique inside
   have nextBound:=Nat.le_trans (update_length group outcome) bounded
   have nextHoles:=List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holes
   have last:=ih nextValid nextUnique nextInside nextBound j nextHero nextLocks nextHoles
   simp only [PaidCount11.count,if_neg headNotPaid,Nat.zero_add,nextMarker]
   exact last

theorem start_hero : (212:Cell)∈region 0:=by decide +kernel
#print axioms quiet_frame
#print axioms quiet_no_north

theorem complete (i : Fin 2) (group : List Cell) (bounded : group.length≤1)
 (inside : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i:=by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group:=by
    intro c h
    rcases List.mem_cons.mp h with rfl|later
    ·exact owner
    ·exact inside later
  have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega

theorem quiet_of_cheap_boundary {state final : State} {history dirs : List Dir}
 {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders)
 (cheapFront : energy state final [213] outcomes<2)
 (noBoundary : PaidCount11.count Gate265Transport11.paid (locks 0) dirs outcomes=0) :
 UpperQuiet11.Quiet paid state (locks 0) dirs final pushes moves outcomes:=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good : OwnedCorral11.Good locks region state (locks 0):=⟨0,hero,fun _ h=>h⟩
 rcases first_cut_or_quiet (paid:=paid) logged (locks 0) with found|quiet
 ·obtain ⟨cut⟩:=found
  obtain ⟨j,heroBefore,selected,tag⟩:=quiet_frame cut.before valid (unique 0) inside (by change ([213] :List Cell).length≤1;decide)
    0 hero (fun _ h=>h) reached.holes_sublist.subset
  have beforeFacts:=cut.before.logged.end_subset valid.1 (locks 0) (unique 0) inside
  have beforeBound:=endGroup_length_le (locks 0) cut.beforeOutcomes
  change (endGroup (locks 0) cut.beforeOutcomes).length≤1 at beforeBound
  have currentReached:=reached.append cut.before.logged.trace
  have currentValid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant currentReached
  obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
  rcases pays with ⟨rfl,sides⟩|⟨rfl,south⟩
  ·have member:=complete j _ beforeBound selected 213 owner
   have row : (List.finRange 2).all (fun j=>decide (213∈locks j→front j=213))=true:=by decide +kernel
   have frontEq:=of_decide_eq_true (List.all_eq_true.mp row j (by simp)) member
   change endGroup [213] cut.beforeOutcomes=[front j] at tag
   rw [frontEq] at tag
   have singletonInside : [213]⊆state.boulders:=List.Subset.trans (by change ([213]:List Cell)⊆[213];decide) inside
   have beforeSmall:=cut.before.logged.end_subset valid.1 [213] (by decide) singletonInside
   have localPaid : UpperLocalPrice11.paid 213 cut.direction:=by
     rcases sides with east|west
     ·rw [east];simp [UpperLocalPrice11.paid,UpperLocalPrice11.eastSources]
     ·rw [west];simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]
   have price:=UpperLocalPrice11.exit_row currentValid beforeSmall.1 beforeSmall.2 cut.headChecked cut.headEffect
     ⟨213,by rw [tag];simp,metadata,localPaid⟩
   have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 1) valid
     [213] (by decide) singletonInside (by decide)
   change 0≤energy state cut.middle [213] cut.beforeOutcomes at prefixNN
   have actual:=step_boulders_nodup _ _ _ _ currentValid.1 cut.headChecked
   have nextUnique:=GhostSubset.update_unique _ _ _ cut.headEffect actual _ beforeSmall.1 beforeSmall.2
   have nextInside:=GhostSubset.update_subset _ _ _ cut.headEffect _ beforeSmall.1 beforeSmall.2
   have nextBound:=Nat.le_trans (update_length (endGroup [213] cut.beforeOutcomes) cut.headOutcome)
     (endGroup_length_le [213] cut.beforeOutcomes)
   have nextValid:=(groupCertificate 1).preserved _ _ _ currentValid cut.headChecked
   have tailNN:=HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 1) nextValid
     _ nextUnique nextInside nextBound
   change 0≤energy cut.actor.state final (update (endGroup [213] cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tailNN
   have append:=energy_append state cut.middle final [213] cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
   have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
     (endGroup [213] cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
   change energy cut.middle final (endGroup [213] cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
     charge NetHack.Soko11Hero315.holeWeight (endGroup [213] cut.beforeOutcomes) cut.headOutcome+
     value cut.actor.state (update (endGroup [213] cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup [213] cut.beforeOutcomes)+
     energy cut.actor.state final (update (endGroup [213] cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
   have all:=congrArg (energy state final [213]) cut.outcomesEq
   exact False.elim (by omega)
  ·have crossing : OwnedCorral11.PaidStep Gate265Transport11.paid
      (endGroup (locks 0) cut.beforeOutcomes) cut.direction cut.actor:=
     ⟨239,owner,metadata,Or.inl ⟨rfl,south⟩⟩
   have count:=PaidCount11.event_le (paid:=Gate265Transport11.paid) (lastDirs:=cut.afterDirs) (last:=cut.afterOutcomes)
     cut.before.logged cut.headEffect (locks 0) crossing
   rw [←cut.dirsEq,←cut.outcomesEq,noBoundary] at count
   omega
 ·exact quiet

theorem no_north_of_cheap_boundary {state final : State} {history dirs : List Dir}
 {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders)
 (cheapFront : energy state final [213] outcomes<2)
 (noBoundary : PaidCount11.count Gate265Transport11.paid (locks 0) dirs outcomes=0) :
 PaidCount11.count FirstRest18711.paid [213] dirs outcomes=0:=by
 have quiet:=quiet_of_cheap_boundary reached logged hero inside cheapFront noBoundary
 exact quiet_no_north quiet (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) (unique 0) inside
   (by change ([213] :List Cell).length≤1;decide) 0 hero (fun _ h=>h) reached.holes_sublist.subset
#print axioms quiet_of_cheap_boundary
#print axioms no_north_of_cheap_boundary

end Owner1007.Pure212Above11

