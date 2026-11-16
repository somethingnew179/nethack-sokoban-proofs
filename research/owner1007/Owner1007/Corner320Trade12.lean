import Owner1007.Corner320Two12
import Owner1007.SurvivorPrefix12
namespace Owner1007.Corner320Trade12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def locks:Fin 8→List Cell
 |0=>[320,345] |1=>[320,319] |2=>[320,293] |3=>[320,371]
 |4=>[320,294] |5=>[320,397] |6=>[320,370] |7=>[]
def region (i:Fin 8):List Cell:=
 if i=2 then Corner320Two12.region 2
 else soko1_2.board.floor.filter fun c=>!(locks i).contains c
def credit:Fin 8→Int |0=>3|1=>3|2=>3|3=>1|4=>3|5=>3|6=>3|7=>0
def target (i:Fin 8) (source:Cell) (dir:Dir):Fin 8:=
 match i.val,source,dir with
 |0,345,.north=>1 |0,345,.south=>3
 |1,319,.north=>2 |1,319,.south=>0
 |2,293,.east=>4
 |3,371,.north=>0 |3,371,.south=>5 |3,371,.west=>6
 |_,_,_=>7
def ShiftAt (i:Fin 8) (source:Cell) (dir:Dir):Prop:=
 ∃dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest]∧dest∉soko1_2.initial.holes∧
 locks (target i source dir)⊆dest::(locks i).erase source∧source∈region (target i source dir)∧
 credit i≤1+p.boulder dest-p.boulder source+credit (target i source dir)
instance (i:Fin 8) (source:Cell) (dir:Dir):Decidable (ShiftAt i source dir):=by unfold ShiftAt;infer_instance
def pushCheck (i:Fin 8) (source:Cell) (dir:Dir):Bool:=
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_2.board (locks i) source dir∨ShiftAt i source dir)
theorem push_rows:∀i,∀source∈locks i,∀dir∈allDirs,pushCheck i source dir=true:=by decide +kernel
theorem floors:∀i,region i⊆soko1_2.board.floor:=by decide +kernel
theorem reverse:Geometry.reverseCheck soko1_2.board=true:=by decide +kernel
theorem unique:∀i,(locks i).Nodup:=by decide +kernel
theorem closed:PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit:=by
 constructor
 ·intro i hero heroInside dir cell adjacent floor door notLock clear
  by_cases special:i=2
  ·subst i
   have ki:locks 2=Corner320Two12.locks 2:=by decide +kernel
   have rr:region 2=Corner320Two12.region 2:=by decide +kernel
   rw[rr] at heroInside ⊢
   rw[ki] at notLock clear
   exact Corner320Two12.closed.1 2 hero heroInside dir cell adjacent floor door notLock clear
  ·unfold region
   rw[if_neg special]
   exact List.mem_filter.mpr ⟨floor,by simpa using notLock⟩
 ·intro i hero heroInside dir source sourceIn adjacent
  have back:=Geometry.reverseCheck_sound soko1_2.board reverse hero (floors i heroInside) dir source adjacent
  have row:=push_rows i source sourceIn dir (Geometry.all_directions dir)
  simp only[pushCheck,back] at row
  rcases of_decide_eq_true row with outside|blocked|shift
  ·exact False.elim (outside heroInside)
  ·exact Or.inl blocked
  ·obtain⟨dest,member,targets,clear,kept,heroNext,paid⟩:=shift
   exact Or.inr ⟨target i source dir,dest,member,targets,clear,kept,heroNext,paid⟩
theorem two_locks:∀i:Fin 8,i≠7→(locks i).length=2:=by decide +kernel
theorem free_credit:credit 7=0:=by decide +kernel
theorem hero319:(319:Cell)∈region 0∧(319:Cell)∈region 2:=by decide +kernel
theorem trade {state final dirs pushes moves outcomes history past pastMoves}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (i:Fin 8) (hero:state.player∈region i) (inside:locks i⊆state.boulders):
 credit i≤energy p (locks i) outcomes∨2≤(endGroup (locks i) outcomes).length:=by
 obtain⟨j,_,kept,paid⟩:=RightPrice4.owned_trace_price closed unique logged reached (locks i) (unique i) inside hero (fun _ h=>h)
 by_cases free:j=7
 ·subst j
  rw[free_credit] at paid
  have debtNN:=NonlinearFacts.weightSum_nonnegative (fun c=>-p.boulder c) (endGroup (locks i) outcomes)
    (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
  change 0≤debtOf p (endGroup (locks i) outcomes) at debtNN
  change credit i≤ownSlack p (locks i) outcomes+0 at paid
  exact Or.inl (by unfold energy;omega)
 ·have count:=List.Nodup.length_le_of_subset (unique j) kept
  rw[two_locks j free] at count
  exact Or.inr count
#print axioms closed
#print axioms trade
end Owner1007.Corner320Trade12
