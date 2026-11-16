import Owner1007.Upper216Eight11
import Owner1007.QuietFixed11
import Owner1007.WestRankHead11
namespace Owner1007.Left188Pocket11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def beforeLocks (i : Fin 2) : List Cell := if i.val=0 then [184,187,212] else [184,186,212]
def beforeRegion (i : Fin 2) : List Cell := LeftPair11.H.filter fun c=>
 !([183,184,185,186,209,210,211,212]++if i.val=0 then [187] else []).contains c
def beforePaid (source : Cell) (dir : Dir) : Prop := source=212 ∨ (source=186 ∧ dir=.west)
instance (c : Cell) (d : Dir) : Decidable (beforePaid c d) := by unfold beforePaid; infer_instance
def afterLocks (_ : Fin 1) : List Cell := [184,186,213]
def afterRegion (_ : Fin 1) : List Cell := LeftPair11.H.filter fun c=>
 decide (c<239 ∨ c%26=24) && !([183,184,185,186,209,210,211,212,213] : List Cell).contains c
def afterPaid (source : Cell) (dir : Dir) : Prop := source=213 ∨ (source=186 ∧ dir=.west)
instance (c : Cell) (d : Dir) : Decidable (afterPaid c d) := by unfold afterPaid; infer_instance

theorem beforeNode0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes beforeLocks beforeRegion beforePaid 0=true := by decide +kernel
theorem beforeNode1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes beforeLocks beforeRegion beforePaid 1=true := by decide +kernel
theorem afterNode : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes afterLocks afterRegion afterPaid 0=true := by decide +kernel
theorem before_floor (i : Fin 2) : beforeRegion i⊆soko1_1.board.floor := by
 have row : (List.finRange 2).all (fun i=>(beforeRegion i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem after_floor (i : Fin 1) : afterRegion i⊆soko1_1.board.floor := by
 have row : (afterRegion 0).all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp row c h)
theorem before_closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes beforeLocks beforeRegion beforePaid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked before_floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1:=by omega
 rcases cases with rfl|rfl
 · exact beforeNode0
 · exact beforeNode1
theorem after_closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes afterLocks afterRegion afterPaid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked after_floor
 intro i
 have same : i=0:=Fin.ext (by omega)
 simpa only [same] using afterNode

def headCheck {n : Nat} (ls rs : Fin n→List Cell) (cell : Cell) (allowed : Dir→Prop) [∀d,Decidable (allowed d)] (i : Fin n) : Bool :=
 allDirs.all fun dir=>match advance soko1_1.board cell dir.opposite with
 |none=>true
 |some hero=>decide (hero∉rs i ∨ BlockedPush soko1_1.board (ls i) cell dir ∨ allowed dir)
theorem beforeHead : (List.finRange 2).all (headCheck beforeLocks beforeRegion 212 (fun d=>d=.west))=true := by decide +kernel
theorem afterHead : headCheck afterLocks afterRegion 213 (fun d=>d=.west ∨ d=.south) 0=true := by decide +kernel

theorem head_allowed {n : Nat} (ls rs : Fin n→List Cell) (cell : Cell) (allowed : Dir→Prop) [∀d,Decidable (allowed d)]
 (i : Fin n) (matrix : headCheck ls rs cell allowed i=true)
 {state : State} {dir : Dir} {t : Transition}
 (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some cell)
 (hero : state.player∈rs i) (floor : state.player∈soko1_1.board.floor)
 (inside : ls i⊆state.boulders) : allowed dir := by
 have adjacent := PairPost11.source_adjacent head metadata
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player floor dir cell adjacent
 have row := List.all_eq_true.mp matrix dir (Geometry.all_directions dir)
 simp only [headCheck,behind] at row
 exact ((of_decide_eq_true row).resolve_left (fun h=>h hero)).resolve_left
   (WestRankHead11.source_unblocked head metadata inside)

theorem west186_impossible {paid state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (present184 : 184∈endGroup group cut.beforeOutcomes)
 (sourceEq : cut.actor.pushSource=some 186) (directionEq : cut.direction=.west)
 (gone : endGroup group outcomes=[]) : False := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have beforeReached := reached.append cut.before.logged.trace
 have beforeFacts := cut.before.logged.end_subset valid.1 group unique inside
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect sourceEq
   (show pushTargets soko1_1.board 186 .west=[185] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 186 (.stay 185)) := by simpa only [headEq] using cut.headEffect
 have nextFacts := Upper216Eight11.next_facts cut reached unique inside bounded
 have afterReached := beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have physical : [184,185]⊆cut.actor.state.boulders := by
   rw [effect.2]
   intro c h
   rcases List.mem_cons.mp h with rfl|later
   · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :184≠186)).mpr (beforeFacts.2 present184))
   · have same : c=185:=List.mem_singleton.mp later
     subst c; exact List.mem_cons_self
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have same : source=186 := Option.some.inj (metadata.symm.trans sourceEq)
 have owns : 185∈Upper216Eight11.next cut := by
   have owner186 : 186∈endGroup group cut.beforeOutcomes := same ▸ owner
   change 185∈update (endGroup group cut.beforeOutcomes) cut.headOutcome
   rw [headEq]
   simp only [update,move,if_pos owner186,post,List.mem_cons]
   exact Or.inl trivial
 exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1
   nextFacts.1 nextFacts.2.1 (Owner1007.locked_of_check _ [184,185] (by decide +kernel)) physical (by decide)
   owns (Upper216Eight11.tail_gone cut gone)

theorem before_forces_left_west {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good beforeLocks beforeRegion state group) (gone : endGroup group outcomes=[]) :
 ∃cut : FirstCut beforePaid state group dirs final pushes moves outcomes,
   cut.actor.pushSource=some 212 ∧ cut.direction=.west ∧ ownPushes [212] cut.beforeOutcomes=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 obtain ⟨cut⟩ := Upper216Eight11.first_any before_closed (by decide +kernel) (by decide +kernel)
   logged valid.1 unique inside good reached.holes_sublist.subset gone
 obtain ⟨i,hero,locks⟩ := Upper216Eight11.quiet_good_any before_closed (by decide +kernel) cut.before
   valid.1 unique inside good reached.holes_sublist.subset
 have beforeReached := reached.append cut.before.logged.trace
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have beforeFacts := cut.before.logged.end_subset valid.1 group unique inside
 have physical := List.Subset.trans locks beforeFacts.2
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 rcases pays with rfl|⟨rfl,west⟩
 · have dirWest := head_allowed beforeLocks beforeRegion 212 (fun d=>d=.west) i
     (List.all_eq_true.mp beforeHead i (by simp)) cut.headChecked metadata hero
     (step_player_clear _ _ _ _ cut.headChecked).1 physical
   obtain ⟨j,_,startLocks⟩:=good
   have start212 : 212∈group := startLocks (show 212∈beforeLocks j from
     of_decide_eq_true (List.all_eq_true.mp (show (List.finRange 2).all (fun j=>decide (212∈beforeLocks j))=true by decide +kernel) j (by simp)))
   exact ⟨cut,metadata,dirWest,cut.before.fixed start212 (by intro d; exact Or.inl rfl)⟩
 · have mem184 : 184∈beforeLocks i := of_decide_eq_true (List.all_eq_true.mp
     (show (List.finRange 2).all (fun i=>decide (184∈beforeLocks i))=true by decide +kernel) i (by simp))
   exact False.elim (west186_impossible cut reached unique inside bounded (locks mem184) metadata west gone)

theorem after_forces_left_exit {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good afterLocks afterRegion state group) (gone : endGroup group outcomes=[]) :
 ∃cut : FirstCut afterPaid state group dirs final pushes moves outcomes,
   cut.actor.pushSource=some 213 ∧ (cut.direction=.west ∨ cut.direction=.south) ∧ ownPushes [213] cut.beforeOutcomes=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 obtain ⟨cut⟩ := Upper216Eight11.first_any after_closed (by decide +kernel) (by decide +kernel)
   logged valid.1 unique inside good reached.holes_sublist.subset gone
 obtain ⟨i,hero,locks⟩ := Upper216Eight11.quiet_good_any after_closed (by decide +kernel) cut.before
   valid.1 unique inside good reached.holes_sublist.subset
 have beforeFacts := cut.before.logged.end_subset valid.1 group unique inside
 have physical := List.Subset.trans locks beforeFacts.2
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 rcases pays with rfl|⟨rfl,west⟩
 · have dirs := head_allowed afterLocks afterRegion 213 (fun d=>d=.west ∨ d=.south) i
     (by have same : i=0:=Fin.ext (by omega); simpa only [same] using afterHead)
     cut.headChecked metadata hero (step_player_clear _ _ _ _ cut.headChecked).1 physical
   obtain ⟨j,_,startLocks⟩:=good
   have start213 : 213∈group := startLocks (by change 213∈([184,186,213] : List Cell); decide)
   exact ⟨cut,metadata,dirs,cut.before.fixed start213 (by intro d; exact Or.inl rfl)⟩
 · exact False.elim (west186_impossible cut reached unique inside bounded (locks (by change 184∈([184,186,213] : List Cell); decide)) metadata west gone)
#print axioms before_forces_left_west
#print axioms after_forces_left_exit

theorem before_left_energy_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good beforeLocks beforeRegion state group) (gone : endGroup group outcomes=[])
 (left : List Cell) (leftUnique : left.Nodup) (leftInside : left⊆state.boulders) (leftBound : left.length≤18)
 (owns212 : 212∈left) :
 2≤energy state final left outcomes := by
 obtain ⟨cut,metadata,west,fixed⟩:=before_forces_left_west reached logged group unique inside bounded good gone
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have beforeReached := reached.append cut.before.logged.trace
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have singletonTag := no_push_unchanged [212] cut.beforeOutcomes fixed
 have singletonInside : [212]⊆state.boulders := by simpa using leftInside owns212
 have selected := cut.before.logged.end_mono valid.1 [212] left (by decide) singletonInside
   (by intro c h; have same : c=212:=List.mem_singleton.mp h; exact same ▸ owns212)
 have beforeFacts := cut.before.logged.end_subset valid.1 left leftUnique leftInside
 have owns : 212∈endGroup left cut.beforeOutcomes := selected (by rw [singletonTag]; simp)
 have pays : OwnedCorral11.PaidStep LeftPair11.paid (endGroup left cut.beforeOutcomes) cut.direction cut.actor :=
   ⟨212,owns,metadata,by simp [LeftPair11.paid,west]⟩
 have row := LeftStrict11.exit_row scalar rfl beforeValid cut.headChecked cut.headEffect beforeFacts.1 beforeFacts.2 pays
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup left cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup left cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup left cut.beforeOutcomes) at row
 have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid left leftUnique leftInside leftBound
 change 0≤energy state cut.middle left cut.beforeOutcomes at prefixNN
 have afterActual:=step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
 have afterUnique:=GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ beforeFacts.1 beforeFacts.2
 have afterInside:=GhostSubset.update_subset _ _ _ cut.headEffect _ beforeFacts.1 beforeFacts.2
 have afterBound:=Nat.le_trans (update_length (endGroup left cut.beforeOutcomes) cut.headOutcome)
   (Nat.le_trans (endGroup_length_le left cut.beforeOutcomes) leftBound)
 have afterValid:=(groupCertificate 18).preserved _ _ _ beforeValid cut.headChecked
 have tailNN:=HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18) afterValid
   _ afterUnique afterInside afterBound
 change 0≤energy cut.actor.state final (update (endGroup left cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tailNN
 have split:=energy_append state cut.middle final left cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup left cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup left cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup left cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup left cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup left cut.beforeOutcomes)+
   energy cut.actor.state final (update (endGroup left cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same:=congrArg (energy state final left) cut.outcomesEq
 omega
#print axioms before_left_energy_two

end Owner1007.Left188Pocket11

