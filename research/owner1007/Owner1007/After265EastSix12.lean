import Owner1007.After265EastPureFive12
namespace Owner1007.After265EastSix12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev locks := After265EastPureFive12.locks
abbrev region := After265EastPureFive12.region
/-- Stronger credits on the same eighteen prescribed local footprints. -/
def credit : Fin 18→Int
 |0=>6
 |1=>7
 |2=>8
 |3=>6
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
 |14=>2
 |15=>3
 |16=>4
 |_=>0
def target (i : Fin 18) (source : Cell) (dir : Dir) : Fin 18 :=
 match i.val,source,dir with
 |0,292,.east=>6
 |0,318,.east=>3
 |0,345,.north=>1
 |1,292,.east=>7
 |1,319,.north=>2
 |2,318,.east=>4
 |2,318,.west=>12
 |3,292,.east=>5
 |3,319,.east=>14
 |4,319,.east=>16
 |5,319,.east=>16
 |6,318,.east=>5
 |6,345,.north=>7
 |9,289,.east=>10
 |10,290,.east=>11
 |10,290,.west=>9
 |11,291,.east=>12
 |11,291,.west=>10
 |12,292,.east=>13
 |12,292,.west=>11
 |13,293,.west=>12
 |14,345,.north=>15
 |15,319,.north=>16
 |15,319,.south=>14
 |_,_,_=>17
def ShiftAt (i : Fin 18) (source : Cell) (dir : Dir) : Prop :=
 ∃ dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest] ∧dest∉soko1_2.initial.holes ∧
 locks (target i source dir)⊆dest::(locks i).erase source ∧source∈region (target i source dir) ∧
 credit i≤1+p.boulder dest-p.boulder source+credit (target i source dir)
instance (i : Fin 18) (source : Cell) (dir : Dir) : Decidable (ShiftAt i source dir) := by unfold ShiftAt;infer_instance
def pushCheck (i : Fin 18) : Bool :=
 (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_2.board (locks i) source dir∨ShiftAt i source dir)
theorem pushes : ∀i,pushCheck i=true := by decide +kernel
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit := by
 constructor
 ·exact After265EastPureFive12.closed.1
 ·intro i hero heroInside dir source sourceInside adjacent
  have row:=List.all_eq_true.mp (List.all_eq_true.mp (pushes i) source sourceInside) dir (Geometry.all_directions dir)
  have behind:=Geometry.reverseCheck_sound soko1_2.board After265EastFive12.reverse hero
   (After265EastPureFive12.floors i heroInside) dir source adjacent
  simp only[pushCheck,behind] at row
  rcases (of_decide_eq_true row).resolve_left (fun h=>h heroInside) with blocked|shifted
  ·exact Or.inl blocked
  ·exact Or.inr ⟨target i source dir,shifted⟩
theorem debt_credit : ∀i,credit i≤debtOf p (locks i) := by decide +kernel

theorem owned_credit {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 18) (hero : state.player∈region i) (inside : locks i⊆group) :
 credit i≤energy p group outcomes := by
 obtain ⟨j,_,kept,price⟩:=RightPrice4.owned_trace_price closed After265EastPureFive12.unique logged reached group gUnique subset hero inside
 have debt:=NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
  (locks j) (endGroup group outcomes)
  (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
  (After265EastPureFive12.unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have bound:=debt_credit j
 change credit i≤ownSlack p group outcomes+credit j at price
 unfold energy
 omega
#print axioms pushes
#print axioms owned_credit
end Owner1007.After265EastSix12
