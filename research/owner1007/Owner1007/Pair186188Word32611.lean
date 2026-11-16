import Owner1007.TightRowPairs32611
import Owner1007.UpperLocalPrice11
import Owner1007.LeftStrict11
namespace Owner1007.Pair186188Word32611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def left (i : Fin 3) : Cell := if i.val=2 then 187 else 186
def right (i : Fin 3) : Cell := if i.val=0 then 188 else 189
def pair (i : Fin 3) : List Cell := [left i,right i]
def exit (source : Cell) (dir : Dir) : Prop := source=189∧dir=.east
instance (source : Cell) (dir : Dir) : Decidable (exit source dir) := by unfold exit;infer_instance
def Shape (i : Fin 3) (source : Cell) (dir : Dir) (dest : Cell) : Prop :=
 (source=left i ∧dir=.west) ∨
 (source=right i ∧exit source dir) ∨
 (∃j : Fin 3,update [left i] (.push source (.stay dest))=[left j] ∧update [right i] (.push source (.stay dest))=[right j]) ∨
 (∃k : Fin 3,TightRowPairs11.pairs k⊆update (pair i) (.push source (.stay dest)))
instance (i : Fin 3) (source : Cell) (dir : Dir) (dest : Cell) : Decidable (Shape i source dir dest) := by unfold Shape;infer_instance
def check (i : Fin 3) : Bool := (pair i).all fun source=>allDirs.all fun dir=>
 (pushTargets soko1_1.board source dir).all fun dest=>decide (dest∉soko1_1.initial.holes ∧Shape i source dir dest)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : (List.finRange 3).all check=true := by decide +kernel
theorem shape (i : Fin 3) (source : Cell) (dir : Dir) (dest : Cell)
 (member : source∈pair i) (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉soko1_1.initial.holes ∧Shape i source dir dest := by
 exact of_decide_eq_true (List.all_eq_true.mp
   (List.all_eq_true.mp (List.all_eq_true.mp checked i (by simp)) source member) dir (Geometry.all_directions dir) |> fun row=>List.all_eq_true.mp row dest target)
theorem unique (i : Fin 3) : (pair i).Nodup := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2 := by omega
 rcases choices with rfl|rfl|rfl
 ·change ([186,188] : List Cell).Nodup;decide +kernel
 ·change ([186,189] : List Cell).Nodup;decide +kernel
 ·change ([187,189] : List Cell).Nodup;decide +kernel
theorem left_cases (i : Fin 3) : left i=186∨left i=187 := by unfold left;split <;> simp_all
theorem right_cases (i : Fin 3) : right i=188∨right i=189 := by unfold right;split <;> simp_all
theorem priced_left {state : State} {dir : Dir} {t : Transition} {outcome : Outcome}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (i : Fin 3) (present : left i∈state.boulders)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (metadata : t.pushSource=some (left i)) (west : dir=.west) :
 2≤charge NetHack.Soko11Hero315.holeWeight [left i] outcome+
   value t.state (update [left i] outcome)-value state [left i] := by
 rcases left_cases i with same|same
 ·have row := LeftStrict11.exit_row (group:=[left i]) scalar rfl valid head effect (by simp) (by simpa using present)
    ⟨left i,by simp,metadata,by rw [same];exact ⟨Or.inr (Or.inl rfl),west⟩⟩
  exact row
 ·exact UpperLocalPrice11.exit_row (group:=[left i]) valid (by simp) (by simpa using present) head effect
    ⟨left i,by simp,metadata,by rw [same,west];simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]⟩

theorem one_step {beforeDirs state beforePushes beforeMoves before dir t outcome dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (tail : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+t.pushCost+pushes≤326)
 (i : Fin 3) (inside : pair i⊆state.boulders)
 (avoid : ¬OwnedCorral11.PaidStep exit [right i] dir t)
 (cheapLeft : charge NetHack.Soko11Hero315.holeWeight [left i] outcome+
   value t.state (update [left i] outcome)-value state [left i]<2) :
 ∃j : Fin 3,update [left i] outcome=[left j] ∧update [right i] outcome=[right j] := by
 cases outcome with
 |walk target=>exact ⟨i,rfl,rfl⟩
 |push source ending=>
  by_cases member : source∈pair i
  ·have metadata : t.pushSource=some source := by
    cases ending with
    |stay target=>rw [effect.2]
    |fill hole=>rw [effect.2.2]
   rcases step_cases_full _ _ _ _ head with walked|pushed
   ·obtain ⟨target,_,_,_,_,form⟩ := walked
    simp only [form] at metadata
    contradiction
   ·obtain ⟨other,result,_,_,_,push,form⟩ := pushed
    have same : other=source := by simpa only [form,Option.some.injEq] using metadata
    subst other
    have spec := pushBoulder_spec _ _ _ _ _ push
    have row := shape i source dir result.landing member spec.2
    have holesInside := first.trace.holes_sublist.subset
    have noFill : result.filled=none := by
     rcases spec.1 with stay|fill
     ·exact stay.1
     ·exact False.elim (row.1 (holesInside fill.2.1))
    have landed : t.landing=some result.landing := by simp only [form]
    have filled : t.filled=none := by simpa only [form] using noFill
    have outcomeEq := CutStrict11.outcome_stay effect metadata landed filled
    have actualEffect : Matches state t (.push source (.stay result.landing)) := by simpa only [outcomeEq] using effect
    rcases row.2 with ⟨same,west⟩|⟨same,pays⟩|next|frozen
    ·have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
     have bound := priced_left valid i (inside (by simp [pair])) head effect (by simpa only [same] using metadata) west
     omega
    ·exact False.elim (avoid ⟨source,by simpa only [List.mem_singleton] using same,metadata,pays⟩)
    ·obtain ⟨j,leftEq,rightEq⟩ := next
     exact ⟨j,by rw [outcomeEq];exact leftEq,by rw [outcomeEq];exact rightEq⟩
    ·obtain ⟨k,locksInside⟩ := frozen
     let one : Logged soko1_1.board state [dir] t.state t.pushCost 1 [.push source ending] :=
       .cons head effect (.nil _)
     let extended := first.append one
     have actual := GhostSubset.update_subset state t (.push source ending) effect (pair i) (unique i) inside
     have physical : TightRowPairs11.pairs k⊆t.state.boulders := List.Subset.trans
       (by simpa only [outcomeEq] using locksInside) actual
     exact False.elim (TightRowPairs32611.excluded extended tail completed cheap k physical)
  ·have notLeft : source∉[left i] := fun h=>member (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))
   have notRight : source∉[right i] := fun h=>member (List.mem_cons_of_mem _ (List.mem_singleton.mpr (List.mem_singleton.mp h)))
   exact ⟨i,by simp only [update,move,if_neg notLeft],by simp only [update,move,if_neg notRight]⟩
#print axioms checked
#print axioms one_step
theorem guard_aux {beforeDirs state beforePushes beforeMoves before group dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (quiet : UpperQuiet11.Quiet exit state group dirs middle pushes moves outcomes)
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last)
 (completed : Goal final) (cheap : beforePushes+pushes+lastPushes≤326)
 (i : Fin 3) (tagEq : group=[right i]) (inside : pair i⊆state.boulders)
 (cheapLeft : energy state middle [left i] outcomes<2) :
 ∃j : Fin 3,endGroup [left i] outcomes=[left j] ∧endGroup group outcomes=[right j] := by
 induction quiet generalizing beforeDirs beforePushes beforeMoves before i with
 |nil=>exact ⟨i,rfl,tagEq⟩
 |@cons state group dir t rest middle pushes moves outcome outcomes head effect avoid tail ih=>
  cases tagEq
  have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
  have nextValid := (groupCertificate 1).preserved _ _ _ valid head
  have actual := step_boulders_nodup _ _ _ _ valid.1 head
  have leftInside : [left i]⊆state.boulders := by
   intro c h
   have same := List.mem_singleton.mp h
   subst c
   exact inside (by simp [pair])
  have leftUnique := GhostSubset.update_unique _ _ _ effect actual [left i] (by simp) leftInside
  have leftSubset := GhostSubset.update_subset _ _ _ effect [left i] (by simp) leftInside
  have leftBound : (update [left i] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
  have tailNN := HeroLedger.Logged.energy_nonnegative tail.logged (groupCertificate 1) nextValid
    (update [left i] outcome) leftUnique leftSubset leftBound
  have row := (groupCertificate 1).row state dir t outcome [left i] valid (by simp) leftInside (by simp) head effect
  have split := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state middle [left i] outcome outcomes
  change 0≤energy t.state middle (update [left i] outcome) outcomes at tailNN
  change value state [left i]≤charge NetHack.Soko11Hero315.holeWeight [left i] outcome+value t.state (update [left i] outcome) at row
  change energy state middle [left i] (outcome::outcomes)=
    charge NetHack.Soko11Hero315.holeWeight [left i] outcome+
      value t.state (update [left i] outcome)-value state [left i]+energy t.state middle (update [left i] outcome) outcomes at split
  have firstCheap : charge NetHack.Soko11Hero315.holeWeight [left i] outcome+
      value t.state (update [left i] outcome)-value state [left i]<2 := by omega
  have stepCheap : beforePushes+t.pushCost+(pushes+lastPushes)≤326 := by omega
  obtain ⟨j,leftEq,rightEq⟩ := one_step first head effect (tail.logged.append suffix) completed stepCheap i inside avoid firstCheap
  have rightInside : [right i]⊆state.boulders := by
   intro c h
   have same := List.mem_singleton.mp h
   subst c
   exact inside (by simp [pair])
  have rightSubset := GhostSubset.update_subset _ _ _ effect [right i] (by simp) rightInside
  have nextInside : pair j⊆t.state.boulders := by
   intro c member
   change c∈[left j,right j] at member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   ·exact leftSubset (by rw [leftEq];simp)
   ·exact rightSubset (by rw [rightEq];simp)
  let one : Logged soko1_1.board state [dir] t.state t.pushCost 1 [outcome] := .cons head effect (.nil _)
  let nextFirst := first.append one
  have nextCheap : beforePushes+t.pushCost+pushes+lastPushes≤326 := by omega
  have tailCheap : energy t.state middle [left j] outcomes<2 := by rw [←leftEq];omega
  obtain ⟨lastIndex,lastLeft,lastRight⟩ := ih nextFirst suffix nextCheap j rightEq nextInside tailCheap
  exact ⟨lastIndex,by simpa only [endGroup,leftEq] using lastLeft,lastRight⟩

theorem prefix_word {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last)
 (completed : Goal final) (cheap : pushes+lastPushes≤326)
 (zero186 : energy soko1_1.initial final [186] (outcomes++last)=0)
 (quiet : UpperQuiet11.Quiet exit soko1_1.initial [188] dirs state pushes moves outcomes) :
 ∃i : Fin 3,endGroup [186] outcomes=[left i] ∧endGroup [188] outcomes=[right i] := by
 have bound := prefix_energy_le prefixLog suffix [186] (by decide) (by decide)
 have currentCheap : energy soko1_1.initial state [186] outcomes<2 := by omega
 exact guard_aux quiet (Logged.nil _) suffix completed (by omega) 0 rfl (by decide) currentCheap
#print axioms guard_aux
#print axioms prefix_word
end Owner1007.Pair186188Word32611
