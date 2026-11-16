import Owner1007.After265EastSix12
namespace Owner1007.After265EastTrade12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def oldIndex (i:Fin 19):Fin 18:=if h:i.val<18 then ⟨i.val,h⟩else 0
def locks (i:Fin 19):List Cell:=if i.val<18 then After265EastPureFive12.locks (oldIndex i) else [320,371]
def region (i:Fin 19):List Cell:=if i.val<18 then After265EastPureFive12.region (oldIndex i)
 else soko1_2.board.floor.filter fun c=>!(locks i).contains c
/-- Stronger credits on the same eighteen prescribed local footprints. -/
def credit : Fin 19→Int
 |0=>7
 |1=>7
 |2=>8
 |3=>7
 |4=>8
 |5=>5
 |6=>5
 |7=>5
 |8=>0
 |9=>4
 |10=>5
 |11=>6
 |12=>5
 |13=>4
 |14=>3
 |15=>3
 |16=>4
 |18=>1
 |_=>0
def target (i:Fin 19) (source:Cell) (dir:Dir):Fin 19:=
 if i.val=14∧source=345∧dir=.south then 18
 else if i.val=18 then (if source=371∧dir=.north then 14 else 17)
 else ⟨(After265EastSix12.target (oldIndex i) source dir).val,by have h:=(After265EastSix12.target (oldIndex i) source dir).isLt;omega⟩
def ShiftAt (i : Fin 19) (source : Cell) (dir : Dir) : Prop :=
 ∃ dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest] ∧dest∉soko1_2.initial.holes ∧
 locks (target i source dir)⊆dest::(locks i).erase source ∧source∈region (target i source dir) ∧
 credit i≤1+p.boulder dest-p.boulder source+credit (target i source dir)
instance (i : Fin 19) (source : Cell) (dir : Dir) : Decidable (ShiftAt i source dir) := by unfold ShiftAt;infer_instance
def pushCheck (i : Fin 19) : Bool :=
 (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_2.board (locks i) source dir∨ShiftAt i source dir)
theorem pushes : ∀i,pushCheck i=true := by decide +kernel
theorem floors:∀i,region i⊆soko1_2.board.floor:=by decide +kernel
theorem unique:∀i,(locks i).Nodup:=by decide +kernel
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit := by
 constructor
 ·intro i hero heroInside dir cell adjacent floor door notLock clear
  by_cases small:i.val<18
  ·have heroOld:hero∈After265EastPureFive12.region (oldIndex i):=by simpa only[region,if_pos small] using heroInside
   have absentOld:cell∉After265EastPureFive12.locks (oldIndex i):=by simpa only[locks,if_pos small] using notLock
   have clearOld:corner soko1_2.board (NetHack.Sokoban.PatternCorrection.project (After265EastPureFive12.locks (oldIndex i))) hero dir=false:=by
     simpa only[locks,if_pos small] using clear
   have next:=After265EastPureFive12.closed.1 (oldIndex i) hero heroOld dir cell adjacent floor door absentOld clearOld
   simpa only[region,if_pos small] using next
  ·unfold region
   rw[if_neg small]
   exact List.mem_filter.mpr ⟨floor,by simpa using notLock⟩
 ·intro i hero heroInside dir source sourceInside adjacent
  have row:=List.all_eq_true.mp (List.all_eq_true.mp (pushes i) source sourceInside) dir (Geometry.all_directions dir)
  have behind:=Geometry.reverseCheck_sound soko1_2.board After265EastFive12.reverse hero
   (floors i heroInside) dir source adjacent
  simp only[pushCheck,behind] at row
  rcases (of_decide_eq_true row).resolve_left (fun h=>h heroInside) with blocked|shifted
  ·exact Or.inl blocked
  ·exact Or.inr ⟨target i source dir,shifted⟩
theorem debt_credit : ∀i:Fin 19,i≠14→credit i≤debtOf p (locks i) := by decide +kernel

theorem owned_trade {state final dirs pushes moves outcomes history past pastMoves}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (uniqueG:group.Nodup) (subset:group⊆state.boulders)
 (i:Fin 19) (hero:state.player∈region i) (inside:locks i⊆group):
 credit i≤energy p group outcomes∨2≤(endGroup group outcomes).length:=by
 obtain⟨j,_,kept,price⟩:=RightPrice4.owned_trace_price closed unique logged reached group uniqueG subset hero inside
 by_cases bad:j=14
 ·subst j
  have count:=List.Nodup.length_le_of_subset (unique 14) kept
  have size:(locks 14).length=2:=by decide +kernel
  rw[size] at count
  exact Or.inr count
 ·have debt:=NonlinearFacts.weightSum_le_of_nodup_subset (fun c=>-p.boulder c) (locks j) (endGroup group outcomes)
    (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega) (unique j) kept
  change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
  have bound:=debt_credit j bad
  change credit i≤ownSlack p group outcomes+credit j at price
  exact Or.inl (by unfold energy;omega)
#print axioms pushes
#print axioms owned_trade
end Owner1007.After265EastTrade12
