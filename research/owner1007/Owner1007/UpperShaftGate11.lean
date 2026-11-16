import Owner1007.Upper216Eight11
import Owner1007.First137RestAnywhere11
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11
namespace Owner1007.UpperShaftGate11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cell (i : Fin 3) : Cell:=if i.val=0 then 164 else if i.val=1 then 138 else 112
def locks (i : Fin 3) : List Cell:=[137,139,cell i]
def region (i : Fin 3) : List Cell:=if i.val=0 then ZeroWord11.lowerTwo
 else if i.val=1 then ZeroWord11.lowerTwo++[164] else ZeroWord11.lowerTwo++[164,138]
def paid (source : Cell) (_ : Dir) : Prop:=source=137∨source=139
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true:=by decide +kernel
theorem floor (i : Fin 3) : region i⊆soko1_1.board.floor:=by
 have row : (List.finRange 3).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem size : ∀i,(locks i).length=3:=by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2:=by omega
 rcases cases with rfl|rfl|rfl
 · exact node0
 · exact node1
 · exact node2

def headCheck (i : Fin 3) : Bool:=([137,139] :List Cell).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i ∨BlockedPush soko1_1.board (locks i) source dir ∨
   (source=137∧dir=.west)∨(source=139∧dir=.east))
theorem heads : (List.finRange 3).all headCheck=true:=by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 3) (hero : state.player∈region i) (inside : locks i⊆state.boulders)
 (sourcePaid : source=137∨source=139)
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) :
 (source=137∧dir=.west)∨(source=139∧dir=.east):=by
 have member : source∈([137,139] :List Cell):=by
   rcases sourcePaid with rfl|rfl <;> simp
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp heads i (by simp)) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact ((of_decide_eq_true row).resolve_left (fun h=>h hero)).resolve_left (WestRankHead11.source_unblocked checked metadata inside)

theorem first_cut {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (i : Fin 3) (hero : state.player∈region i) (inside : locks i⊆state.boulders) :
 Nonempty (FirstCut paid state (locks i) dirs final pushes moves outcomes):=by
 rcases first_cut_or_quiet (paid:=paid) logged (locks i) with found|quiet
 · exact found
 · have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have good : OwnedCorral11.Good locks region state (locks i):=⟨i,hero,fun _ h=>h⟩
   obtain ⟨j,_,selected⟩:=Upper216Eight11.quiet_good_any closed unique quiet valid.1 (unique i) inside good reached.holes_sublist.subset
   have finalInside:=(logged.end_subset valid.1 (locks i) (unique i) inside).2
   have card:=List.Nodup.length_le_of_subset (unique j) (List.Subset.trans selected finalInside)
   rw [size j] at card
   have conservation:=(reached.append logged.trace).conservation
   have empty : final.holes=[]:=completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   omega

theorem impossible {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCheap : energy soko1_1.initial final U6 (before++outcomes)<8)
 (restCheap : energy soko1_1.initial final Rest (before++outcomes)<2)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (i : Fin 3) (hero : state.player∈region i) (inside : locks i⊆state.boulders) : False:=by
 let logged:=first.append last
 obtain ⟨cut⟩:=first_cut first.trace last completed i hero inside
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have good : OwnedCorral11.Good locks region state (locks i):=⟨i,hero,fun _ h=>h⟩
 obtain ⟨j,heroBefore,locksBefore⟩:=Upper216Eight11.quiet_good_any closed unique cut.before
   valid.1 (unique i) inside good first.trace.holes_sublist.subset
 have beforeFacts:=cut.before.logged.end_subset valid.1 (locks i) (unique i) inside
 have beforePhysical:=List.Subset.trans locksBefore beforeFacts.2
 have currentFirst:=first.append cut.before.logged
 have allEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by
   calc
     _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by simp only [List.append_assoc]
     _=before++outcomes:=congrArg (List.append before) cut.outcomesEq.symm
 have stationarity : ∀c∈([137,139] :List Cell), ownPushes [c] (before++cut.beforeOutcomes)=0:=by
   intro c member
   have inLocks : c∈locks i:=by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> simp [locks]
   have localZero:=cut.before.fixed inLocks (by
     intro d
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> simp [paid])
   have initialZero : ownPushes [c] before=0:=by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl
     · exact zero137
     · exact zero139
   rw [ownPushes_append,no_push_unchanged _ _ initialZero,initialZero,localZero]
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 rcases head_shape j heroBefore beforePhysical pays cut.headChecked metadata with ⟨rfl,west⟩|⟨rfl,east⟩
 · have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)):=by simpa only [headEq] using cut.headEffect
   have reserve:=First137RestAnywhere11.rest_two currentFirst checked effect cut.after completed (stationarity 137 (by simp))
   have eq:=allEffects
   rw [headEq] at eq
   rw [eq] at reserve
   omega
 · have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)):=by simpa only [headEq] using cut.headEffect
   have whole141:=UpperEightBudget11.cheap_others_six logged completed upperCheap 141 (by decide)
   have prefixBound:=prefix_energy_le currentFirst (Logged.cons cut.headChecked cut.headEffect cut.after) [141] (by decide) (by decide)
   rw [allEffects] at prefixBound
   have cheap141 : energy soko1_1.initial cut.middle [141] (before++cut.beforeOutcomes)<6:=by omega
   have survives:=StationaryExitSix11.survives139 currentFirst checked effect cut.after (stationarity 139 (by simp)) cheap141
   have eq:=allEffects
   rw [headEq] at eq
   have wholeSurvives : endGroup [139] (before++outcomes)≠[]:=by rw [←eq];exact survives
   exact UpperEightExit11.survivor_eight_absurd logged completed upperCheap 139 (by simp) wholeSurvives
#print axioms impossible

theorem gate_moved_before_north {state final : State} {t : Transition}
 {beforeDirs afterDirs : List Dir} {beforePushes beforeMoves afterPushes afterMoves : Nat} {before after : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .north=some t) (effect : Matches state t (.push 190 (.stay 164)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (upperCheap : energy soko1_1.initial final U6 (before++.push 190 (.stay 164)::after)<8)
 (restCheap : energy soko1_1.initial final Rest (before++.push 190 (.stay 164)::after)<2) :
 0<ownPushes [137] before ∨0<ownPushes [139] before:=by
 by_cases zero137 : ownPushes [137] before=0
 · by_cases zero139 : ownPushes [139] before=0
   · let headLogged : Logged soko1_1.board state [.north] t.state t.pushCost 1 [.push 190 (.stay 164)]:=
       .cons head effect (.nil _)
     let extended:=first.append headLogged
     have tag137:=no_push_unchanged [137] before zero137
     have tag139:=no_push_unchanged [139] before zero139
     have facts137:=first.end_subset (by decide) [137] (by decide) (by decide)
     have facts139:=first.end_subset (by decide) [139] (by decide) (by decide)
     have extended137 : ownPushes [137] (before++[.push 190 (.stay 164)])=0:=by
       rw [ownPushes_append,tag137]
       simpa [ownPushes,ownPush] using zero137
     have extended139 : ownPushes [139] (before++[.push 190 (.stay 164)])=0:=by
       rw [ownPushes_append,tag139]
       simpa [ownPushes,ownPush] using zero139
     have physical : locks 0⊆t.state.boulders:=by
       change [137,139,164]⊆t.state.boulders
       rw [effect.2]
       intro c h
       simp only [List.mem_cons,List.not_mem_nil,or_false] at h
       rcases h with rfl|rfl|rfl
       · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :137≠190)).mpr (facts137.2 (by rw [tag137];simp)))
       · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :139≠190)).mpr (facts139.2 (by rw [tag139];simp)))
       · exact List.mem_cons_self
     have hero : t.state.player∈region 0:=by
       have same : t.state.player=190:=by rw [effect.2]
       rw [same]
       decide +kernel
     have sequence : (before++[.push 190 (.stay 164)])++after=before++.push 190 (.stay 164)::after:=by
       simp only [List.append_assoc,List.singleton_append]
     have upper : energy soko1_1.initial final U6 ((before++[.push 190 (.stay 164)])++after)<8:=by
       rw [sequence];exact upperCheap
     have rest : energy soko1_1.initial final Rest ((before++[.push 190 (.stay 164)])++after)<2:=by
       rw [sequence];exact restCheap
     exact False.elim (impossible extended last completed upper rest extended137 extended139 0 hero physical)
   · exact Or.inr (by omega)
 · exact Or.inl (by omega)
#print axioms gate_moved_before_north

end Owner1007.UpperShaftGate11

