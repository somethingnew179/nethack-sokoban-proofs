import Owner1007.EastCorral12
import Owner1007.PricedCorral
import NetHack.Sokoban12CostPartition.LowerBound

namespace Owner1007.EastPrice225
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection
open Owner1007
namespace CP
abbrev cert := NetHack.Sokoban12CostPartition.certificate
end CP
abbrev raw := Generated.soko1_2Potential
def W (s : State) : Int := PatternCorrection.value CP.cert s
def locks (i : Fin 7) : List Cell :=
  if h : i.val < 6 then EastCorral12.locks ⟨i.val,h⟩ else []
def region (i : Fin 7) : List Cell :=
  if h : i.val < 6 then EastCorral12.region ⟨i.val,h⟩ else soko1_2.board.floor
def credit (i : Fin 7) : Int := Int.ofNat (6-i.val)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem geometry : PricedCorral.check soko1_2.board soko1_2.initial.holes raw locks region credit = true := by
  decide +kernel
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes raw locks region credit :=
  PricedCorral.closed_of_check _ _ _ _ _ _ geometry
theorem unique : ∀ i : Fin 7, (locks i).Nodup := by decide +kernel
def defaults : List Cell := [296,322,348,371,372,373,374,400]
theorem default_bonus (hero : Cell) (member : hero ∈ defaults) (p : Pattern) :
    NetHack.Sokoban12CostPartition.bonus hero p = NetHack.Sokoban12CostPartition.d258 p := by
  have choices : hero = 296 ∨ hero = 322 ∨ hero = 348 ∨ hero = 371 ∨ hero = 372 ∨
      hero = 373 ∨ hero = 374 ∨ hero = 400 := by simpa [defaults] using member
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem flat_guard : ∀ i : Fin 7, ∀ hero ∈ region i, ∀ dir ∈ allDirs, ∀ source ∈ locks i,
    advance soko1_2.board hero dir = some source →
    ¬ BlockedPush soko1_2.board (locks i) source dir →
    hero ∈ defaults ∧ source ∈ defaults ∧ source ∉ NetHack.Sokoban12CostPartition.support ∧
      ∀ dest ∈ pushTargets soko1_2.board source dir,
        dest ∉ NetHack.Sokoban12CostPartition.support ∧ dest ∉ soko1_2.initial.holes := by decide +kernel

theorem correction_flat {state : State} {i : Fin 7} {dir : Dir} {t : Transition}
    (good : PricedCorral.Good locks region i state)
    (oldGood : PatternCorrection.Good soko1_2.board soko1_2.initial.holes 2 state)
    (holesInside : state.holes ⊆ soko1_2.initial.holes)
    (checked : step soko1_2.board state dir = some t)
    (source : Cell) (result : PushResult)
    (adjacent : advance soko1_2.board state.player dir = some source)
    (push : pushBoulder soko1_2.board state source dir = some result)
    (shape : t = {state := {player := source, boulders := result.boulders, holes := afterFill state.holes result.filled}, pushed := true, filled := result.filled, pushSource := some source, landing := some result.landing})
    (member : source ∈ locks i) :
    PatternCorrection.correction CP.cert state = PatternCorrection.correction CP.cert t.state := by
  have first := push_first_clear soko1_2.board state source dir result push
  have never : ¬ BlockedPush soko1_2.board (locks i) source dir := by
    intro blocked
    rcases blocked with diagonal | blocked
    · simp [first.1] at diagonal
    · obtain ⟨dest,next,floor,door,empty⟩ := first.2
      simp only [next] at blocked
      rcases blocked with wall | door' | box
      · exact wall floor
      · exact door door'
      · exact empty (good.2 box)
  have frame := flat_guard i state.player good.1 dir (Geometry.all_directions dir) source member adjacent never
  have land := frame.2.2.2 result.landing (pushBoulder_spec _ _ _ _ _ push).2
  have unfilled : result.filled = none := by
    rcases (pushBoulder_spec _ _ _ _ _ push).1 with stay | fill
    · exact stay.1
    · exact False.elim (land.2 (holesInside fill.2.1))
  have boxes : result.boulders = result.landing :: state.boulders.erase source :=
    ((pushBoulder_spec _ _ _ _ _ push).1.resolve_right (by intro fill; exact land.2 (holesInside fill.2.1))).2
  have nextGood := PatternCorrection.step_good soko1_2.board soko1_2.initial.holes 2 state dir t oldGood checked
  have agree : Agree NetHack.Sokoban12CostPartition.support
      (project state.boulders) (project (result.landing :: state.boulders.erase source)) := by
    rw [project_replace state.boulders oldGood.1 source result.landing]
    intro cell inside
    have one : source ≠ cell := by intro eq; exact frame.2.2.1 (eq ▸ inside)
    have two : result.landing ≠ cell := by intro eq; exact land.1 (eq ▸ inside)
    simp [change,one,two]
  have same := NetHack.Sokoban12CostPartition.respects source _ _ agree
  have heroes := (default_bonus state.player frame.1 (project state.boulders)).trans
    (default_bonus source frame.2.1 (project state.boulders)).symm
  unfold PatternCorrection.correction
  have oldCertGood : PatternCorrection.Good soko1_2.board soko1_2.initial.holes CP.cert.allowance state := oldGood
  have nextCertGood : PatternCorrection.Good soko1_2.board soko1_2.initial.holes CP.cert.allowance t.state := nextGood
  rw [if_pos oldCertGood,if_pos nextCertGood]
  change NetHack.Sokoban12CostPartition.bonus state.player (project state.boulders) =
    NetHack.Sokoban12CostPartition.bonus t.state.player (project t.state.boulders)
  simp only [shape,boxes]
  exact heroes.trans same

theorem price_step {state : State} {i : Fin 7} {dir : Dir} {t : Transition}
    (good : PricedCorral.Good locks region i state)
    (oldGood : PatternCorrection.Good soko1_2.board soko1_2.initial.holes 2 state)
    (checked : step soko1_2.board state dir = some t) :
    ∃ j, PricedCorral.Good locks region j t.state ∧
      credit i ≤ Int.ofNat t.pushCost + W t.state - W state + credit j := by
  have oldBound := PatternCorrection.stepBound CP.cert Generated.soko1_2_potential_valid state dir t checked
  change W state ≤ Int.ofNat t.pushCost + W t.state at oldBound
  have smallCorner := GhostProjection.original_corner_projected soko1_2.board state (locks i) good.2 dir t checked
  rcases step_cases_full soko1_2.board state dir t checked with walked | pushed
  · obtain ⟨target,adjacent,floor,clear,_,shape⟩ := walked
    have door := FiniteTopology.step_target_not_door soko1_2.board state dir t target adjacent checked
    have notLock : target ∉ locks i := fun h => clear (good.2 h)
    have targetInside := closed.1 i state.player good.1 dir target adjacent floor door notLock smallCorner
    refine ⟨i, ⟨by simpa only [shape] using targetInside, by simpa only [shape] using good.2⟩, ?_⟩
    omega
  · obtain ⟨source,result,adjacent,sourceFloor,present,push,shape⟩ := pushed
    by_cases member : source ∈ locks i
    · obtain ⟨j,next,price⟩ := PricedCorral.step_price closed unique Generated.soko1_2_potential_valid good oldGood.2.1 checked
      change credit i ≤ Int.ofNat t.pushCost + raw.value t.state - raw.value state + credit j at price
      have flat := correction_flat good oldGood oldGood.2.1 checked source result adjacent push shape member
      have delta : W t.state - W state = raw.value t.state - raw.value state := by
        unfold W PatternCorrection.value
        change (raw.value t.state + PatternCorrection.correction CP.cert t.state) -
          (raw.value state + PatternCorrection.correction CP.cert state) = raw.value t.state - raw.value state
        rw [←flat]
        omega
      exact ⟨j,next,by omega⟩
    · have door := FiniteTopology.step_target_not_door soko1_2.board state dir t source adjacent checked
      have sourceInside := closed.1 i state.player good.1 dir source adjacent sourceFloor door member smallCorner
      have erased : locks i ⊆ state.boulders.erase source := by
        intro c inside
        have different : c ≠ source := by intro eq; exact member (eq ▸ inside)
        exact (List.mem_erase_of_ne different).mpr (good.2 inside)
      refine ⟨i, ⟨by simpa only [shape] using sourceInside, ?_⟩, by omega⟩
      simp only [shape]
      change locks i ⊆ result.boulders
      rcases (pushBoulder_spec _ _ _ _ _ push).1 with stay | fill
      · rw [stay.2]
        exact fun _ h => List.mem_cons_of_mem _ (erased h)
      · rw [fill.2.2]
        exact erased

theorem price_trace {state final : State} {dirs : List Dir} {pushes moves : Nat}
    (trace : Trace soko1_2.board state dirs final pushes moves) {i : Fin 7}
    (good : PricedCorral.Good locks region i state)
    (oldGood : PatternCorrection.Good soko1_2.board soko1_2.initial.holes 2 state) :
    ∃ j, PricedCorral.Good locks region j final ∧
      PatternCorrection.Good soko1_2.board soko1_2.initial.holes 2 final ∧
      credit i ≤ Int.ofNat pushes + W final - W state + credit j := by
  induction trace generalizing i with
  | nil current => exact ⟨i,good,oldGood,by simp⟩
  | cons head tail ih =>
    obtain ⟨j,next,one⟩ := price_step good oldGood head
    have nextOld := PatternCorrection.step_good _ _ _ _ _ _ oldGood head
    obtain ⟨k,last,lastOld,later⟩ := ih next nextOld
    refine ⟨k,last,lastOld,?_⟩
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at *
    omega

theorem terminal_credit {state : State} {i : Fin 7}
    (good : PricedCorral.Good locks region i state)
    (oldGood : PatternCorrection.Good soko1_2.board soko1_2.initial.holes 2 state)
    (completed : Goal state) : credit i = 0 := by
  by_cases early : i.val < 6
  · have count := List.Nodup.length_le_of_subset (unique i) good.2
    have size : (locks i).length = 4 := by
      simp only [locks,dif_pos early]
      exact EastCorral12.sizes ⟨i.val,early⟩
    rw [size] at count
    have mass := oldGood.2.2.2
    have empty : state.holes = [] := completed
    rw [empty] at mass
    simp only [List.length_nil] at mass
    omega
  · have val : i.val = 6 := by have h := i.isLt; omega
    simp [credit,val]

def afterE : State :=
  {player := 371, boulders := 372 :: soko1_2.initial.boulders.erase 371, holes := soko1_2.initial.holes}
theorem afterE_value : W afterE = 218 := by decide +kernel
theorem afterE_good : PricedCorral.Good locks region 0 afterE := by constructor <;> decide +kernel
theorem afterE_old : PatternCorrection.Good soko1_2.board soko1_2.initial.holes 2 afterE := by decide +kernel

/-- Universal suffix lower bound from the exact east-first original state. -/
theorem east_suffix_224 {dirs final pushes moves}
    (trace : Trace soko1_2.board afterE dirs final pushes moves) (completed : Goal final) :
    224 ≤ pushes := by
  obtain ⟨j,last,lastOld,bound⟩ := price_trace trace afterE_good afterE_old
  have zero := terminal_credit last lastOld completed
  have lastValue := PatternCorrection.goalBound CP.cert Generated.soko1_2_potential_valid final completed
  change W final ≤ 0 at lastValue
  have six : credit 0 = 6 := rfl
  rw [afterE_value,six,zero] at bound
  simp only [Int.ofNat_eq_natCast] at bound
  omega

theorem east_branch_225 {dirs final pushes moves}
    (trace : Trace soko1_2.board afterE dirs final pushes moves) (completed : Goal final) :
    225 ≤ 1 + pushes := by
  have h := east_suffix_224 trace completed
  omega

#print axioms correction_flat
#print axioms east_suffix_224
#print axioms east_branch_225
end Owner1007.EastPrice225
