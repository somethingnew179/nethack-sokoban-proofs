import Owner1007.UpperAfter187Bound12
import Owner1007.Corner320Trade12
namespace Owner1007.Upper108134Four12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
def locks:Fin 8→List Cell
 |0=>[108,134,158,159]|1=>[108,134,132,159]|2=>[108,134,132,160]
 |3=>[108,133,134]|4=>[108,134]|5=>[158,133]|6=>[132,133]|7=>[]
def region (i:Fin 8):List Cell:=
 if i=5 then UpperAfter18712.region 6 else soko1_2.board.floor.filter fun c=>!(locks i).contains c
def credit:Fin 8→Int|0=>4|1=>4|2=>4|3=>4|4=>2|5=>2|6=>2|7=>0
def target (i:Fin 8) (source:Cell) (dir:Dir):Fin 8:=
 match i.val,source,dir with
 |0,158,.north=>1
 |0,159,.north=>3
 |1,132,.east=>3
 |1,159,.north=>3
 |1,159,.east=>2
 |2,132,.east=>3
 |0,134,.west=>5
 |1,134,.west=>6
 |2,134,.west=>6
 |5,158,.north=>6
 |0,134,_=>7|1,134,_=>7|2,134,_=>7
 |0,_,_=>4|1,_,_=>4|2,_,_=>4
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
theorem unique:∀i,(locks i).Nodup:=by decide +kernel
theorem floors:∀i,region i⊆soko1_2.board.floor:=by decide +kernel
theorem debt_credit:∀i,credit i≤debtOf p (locks i):=by decide +kernel
theorem closed:PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit:=by
 constructor
 ·intro i hero heroInside dir cell adjacent floor door notLock clear
  by_cases special:i=5
  ·subst i
   have ki:locks 5=UpperAfter18712.locks 6:=by decide +kernel
   have rr:region 5=UpperAfter18712.region 6:=by decide +kernel
   rw[rr] at heroInside ⊢
   rw[ki] at notLock clear
   exact (PricedCorral.closed_of_check _ _ _ _ _ _ UpperAfter18712.matrix).1 6 hero heroInside dir cell adjacent floor door notLock clear
  ·unfold region
   rw[if_neg special]
   exact List.mem_filter.mpr ⟨floor,by simpa using notLock⟩
 ·intro i hero heroInside dir source sourceIn adjacent
  have back:=Geometry.reverseCheck_sound soko1_2.board Corner320Trade12.reverse hero (floors i heroInside) dir source adjacent
  have row:=push_rows i source sourceIn dir (Geometry.all_directions dir)
  simp only[pushCheck,back] at row
  rcases of_decide_eq_true row with outside|blocked|shift
  ·exact False.elim (outside heroInside)
  ·exact Or.inl blocked
  ·obtain⟨dest,member,targets,clear,kept,heroNext,paid⟩:=shift
   exact Or.inr ⟨target i source dir,dest,member,targets,clear,kept,heroNext,paid⟩
theorem owned_credit {state final dirs pushes moves outcomes history past pastMoves}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (uniqueG:group.Nodup) (subset:group⊆state.boulders)
 (i:Fin 8) (hero:state.player∈region i) (inside:locks i⊆group):credit i≤energy p group outcomes:=by
 obtain⟨j,_,kept,price⟩:=RightPrice4.owned_trace_price closed unique logged reached group uniqueG subset hero inside
 have debt:=NonlinearFacts.weightSum_le_of_nodup_subset (fun c=>-p.boulder c) (locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega) (unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have bound:=debt_credit j
 change credit i≤ownSlack p group outcomes+credit j at price
 unfold energy
 omega
#print axioms push_rows
#print axioms owned_credit
end Owner1007.Upper108134Four12
