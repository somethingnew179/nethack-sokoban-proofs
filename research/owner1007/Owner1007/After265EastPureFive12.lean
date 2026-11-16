import Owner1007.After265EastFive12
import Owner1007.Corner320Two12
namespace Owner1007.After265EastPureFive12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def legacy (i : Fin 18) : Fin 16 := ⟨if i.val<14 then i.val else 15,by split <;>omega⟩
def cornerIndex (i : Fin 18) : Fin 4 := ⟨if 14≤i.val then i.val-14 else 3,by split <;>omega⟩
def locks (i : Fin 18) : List Cell :=
 if i.val<14 then After265EastFive12.locks (legacy i) else Corner320Two12.locks (cornerIndex i)
def region (i : Fin 18) : List Cell :=
 if i.val<14 then After265EastFive12.region (legacy i) else Corner320Two12.region (cornerIndex i)
def credit (i : Fin 18) : Int :=
 if i.val<14 then After265EastFive12.credit (legacy i) else Corner320Two12.credit (cornerIndex i)
def target (i : Fin 18) (source : Cell) (dir : Dir) : Fin 18 :=
 if i.val<14 then
   let j:=After265EastFive12.target (legacy i) source dir
   if j.val=14 then (if i.val=3 then 14 else 16) else
   if j.val=15 then 17 else ⟨j.val,by have h:=j.isLt;omega⟩
 else if i.val=14∧source=345∧dir=.north then 15 else
 if i.val=15∧source=319∧dir=.north then 16 else 17
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
/-- Only the small deterministic push rows are new; all14 old walking rows are reused. -/
theorem pushes : ∀ i,pushCheck i=true := by decide +kernel
theorem floors : ∀ i,region i⊆soko1_2.board.floor := by
 intro i
 by_cases old:i.val<14
 · simpa only [region,if_pos old] using After265EastFive12.floors (legacy i)
 · simp only [region,if_neg old,Corner320Two12.region]
   intro c member
   exact (List.mem_filter.mp member).1
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit := by
 constructor
 · intro i hero heroInside dir cell adjacent floor door notLock clear
   by_cases old:i.val<14
   · simp only [locks,region,if_pos old] at heroInside notLock clear ⊢
     exact After265EastFive12.closed.1 (legacy i) hero heroInside dir cell adjacent floor door notLock clear
   · simp only [locks,region,if_neg old] at heroInside notLock clear ⊢
     exact Corner320Two12.closed.1 (cornerIndex i) hero heroInside dir cell adjacent floor door notLock clear
 · intro i hero heroInside dir source sourceInside adjacent
   have row := List.all_eq_true.mp (List.all_eq_true.mp (pushes i) source sourceInside)
     dir (Geometry.all_directions dir)
   have behind := Geometry.reverseCheck_sound soko1_2.board After265EastFive12.reverse hero
     (floors i heroInside) dir source adjacent
   simp only [pushCheck,behind] at row
   rcases (of_decide_eq_true row).resolve_left (fun h=>h heroInside) with blocked|shifted
   ·exact Or.inl blocked
   ·exact Or.inr ⟨target i source dir,shifted⟩
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem debt_credit : ∀ i,credit i≤debtOf p (locks i) := by decide +kernel
theorem initial : ∀ i:Fin 3,locks ⟨i.val,by omega⟩=After265EastFive12.locks ⟨i.val,by omega⟩ ∧
 region ⟨i.val,by omega⟩=After265EastFive12.region ⟨i.val,by omega⟩ ∧credit ⟨i.val,by omega⟩=5 := by decide +kernel

theorem owned_five {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 18} (positive : credit i=5) (hero : state.player∈region i) (inside : locks i⊆group) :
 5≤energy p group outcomes := by
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed unique
   logged reached group gUnique subset hero inside
 have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
   (locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
   (unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have creditBound := debt_credit j
 rw [positive] at price
 change 5≤ownSlack p group outcomes+credit j at price
 unfold energy
 omega
#print axioms pushes
#print axioms owned_five
end Owner1007.After265EastPureFive12
