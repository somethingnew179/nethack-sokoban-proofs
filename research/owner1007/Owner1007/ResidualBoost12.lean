import Owner1007.Residual290Any12
import Owner1007.Post187Seven12
namespace Owner1007.ResidualBoost12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def legacy (i:Fin 9):Fin 6:=⟨if i.val<6 then i.val else 5,by split <;>omega⟩
def locks (i:Fin 9):List Cell:=
 if i.val<6 then Residual29012.locks (legacy i) else
 if i=6 then [288,289] else if i=7 then [262,288] else [289,290]
def region (i:Fin 9):List Cell:=
 if i.val<6 then Residual29012.region (legacy i) else
 soko1_2.board.floor.filter fun c=>!(locks i).contains c
def credit:Fin 9→Int |0=>7 |1=>7 |2=>5 |3=>10 |4=>13 |5=>0 |6=>4 |7=>6 |8=>9
def target (i:Fin 9) (source:Cell) (dir:Dir):Fin 9:=
 match i.val,source,dir with
 |0,236,.south=>1
 |0,263,.west=>4
 |0,290,.west=>2
 |1,262,.south=>5
 |1,263,.south=>8
 |1,290,.west=>3
 |2,236,.south=>3
 |2,263,.west=>4
 |2,289,.west=>5
 |3,262,.south=>6
 |3,289,.west=>7
 |_,_,_=>5
def ShiftAt (i:Fin 9) (source:Cell) (dir:Dir):Prop:=
 ∃dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest] ∧dest∉soko1_2.initial.holes ∧
 locks (target i source dir)⊆dest::(locks i).erase source ∧source∈region (target i source dir) ∧
 credit i≤1+p.boulder dest-p.boulder source+credit (target i source dir)
instance (i:Fin 9) (source:Cell) (dir:Dir):Decidable (ShiftAt i source dir):=by unfold ShiftAt;infer_instance
def pushCheck (i:Fin 9):Bool:=
 (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_2.board (locks i) source dir∨ShiftAt i source dir)
/-- Nine manually specified phases: the existing six residual footprints plus
three frozen pairs. Only the small push rows change. -/
theorem pushes:∀i,pushCheck i=true:=by decide +kernel
theorem floors:∀i,region i⊆soko1_2.board.floor:=by
 intro i c member
 by_cases old:i.val<6
 ·simp only[region,if_pos old,Residual29012.region] at member
  exact (List.mem_filter.mp member).1
 ·simp only[region,if_neg old] at member
  exact (List.mem_filter.mp member).1
theorem closed:PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit:=by
 have oldClosed:=PricedCorral.closed_of_check _ _ _ _ _ _ Residual29012.matrix
 constructor
 ·intro i hero heroInside dir cell adjacent floor door notLock clear
  by_cases old:i.val<6
  ·simp only[locks,region,if_pos old] at heroInside notLock clear ⊢
   exact oldClosed.1 (legacy i) hero heroInside dir cell adjacent floor door notLock clear
  ·simp only[region,if_neg old]
   exact List.mem_filter.mpr ⟨floor,by simpa using notLock⟩
 ·intro i hero heroInside dir source sourceInside adjacent
  have row:=List.all_eq_true.mp (List.all_eq_true.mp (pushes i) source sourceInside) dir (Geometry.all_directions dir)
  have behind:=Geometry.reverseCheck_sound soko1_2.board Post187Seven12.reverse hero
    (floors i heroInside) dir source adjacent
  simp only[pushCheck,behind] at row
  rcases (of_decide_eq_true row).resolve_left (fun h=>h heroInside) with blocked|shifted
  ·exact Or.inl blocked
  ·exact Or.inr ⟨target i source dir,shifted⟩
theorem unique:∀i,(locks i).Nodup:=by decide +kernel
theorem debt_credit:∀i,credit i≤debtOf p (locks i):=by decide +kernel

theorem owned_credit {state final dirs pushes moves outcomes}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir} {past pastMoves:Nat}
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (gUnique:group.Nodup) (subset:group⊆state.boulders)
 (i:Fin 9) (hero:state.player∈region i) (inside:locks i⊆group):
 credit i≤energy p group outcomes:=by
 obtain ⟨j,_,kept,price⟩:=RightPrice4.owned_trace_price closed unique logged reached group gUnique subset hero inside
 have debt:=NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
   (locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
   (unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have terminal:=debt_credit j
 change credit i≤ownSlack p group outcomes+credit j at price
 unfold energy
 omega
#print axioms pushes
#print axioms owned_credit
end Owner1007.ResidualBoost12
