import Owner1007.LeftInwardStart11Data
import Owner1007.LeftInwardPipe11Proof
import Owner1007.First137RestAnywhere11
import Owner1007.Gate139EastImpossible11
namespace Owner1007.LeftInwardStart11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem noMove (i : Fin 2) : ∀hero∈region i,∀source∈locks i,∀dir,
 advance soko1_1.board hero dir=some source→BlockedPush soko1_1.board (locks i) source dir∨paid source dir := by
 intro hero member source owner dir adjacent
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (moves i) source owner) dir (Geometry.all_directions dir)
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i member) dir source adjacent
 simp only [moveCheck,behind] at row
 by_cases blocked : BlockedPush soko1_1.board (locks i) source dir
 ·exact Or.inl blocked
 ·exact Or.inr (of_decide_eq_true row member blocked)

theorem phase_closed
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (i : Fin 2) :
 PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
  (fun _ : Fin 1=>locks i) (fun _ : Fin 1=>region i) paid := by
 constructor
 ·intro j hero member dir target adjacent isFloor door notLock corner
  exact closed.1 i hero member dir target adjacent isFloor door notLock corner
 ·intro j hero member dir source owner adjacent
  rcases noMove i hero member source owner dir adjacent with blocked|pays
  ·exact Or.inl blocked
  ·exact Or.inr (Or.inl pays)

theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 2) (hero : state.player∈region i) (physical : locks i⊆state.boulders)
 (pays : paid source dir) (checked : step soko1_1.board state dir=some t)
 (metadata : t.pushSource=some source) : Shape source dir := by
 have member : source∈([137,138,139]:List Cell) := by
  simpa only [paid,List.mem_cons,List.not_mem_nil,or_false] using pays
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (heads i) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata physical) pays

theorem future_four_with
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (pipeClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LeftInwardPipe11.locks LeftInwardPipe11.region LeftInwardPipe11.paid)
 {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (i : Fin 2) (stationary : ownPushes [other i] before=0)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (same : group.Perm (locks i)) (hero : state.player∈region i)
 (gone : endGroup group outcomes=[]) : 4≤energy state final group outcomes := by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have good : OwnedCorral11.Good locks region state group := ⟨i,hero,fun _ h=>same.mem_iff.mpr h⟩
 have bounded : group.length≤18 := by have len:=same.length_eq;change group.length=5 at len;omega
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged valid.1 uniqueGroup inside good first.trace.holes_sublist.subset gone
 have quiet:=LeftQuietIdentity11.quiet_zero_static (locks i) (region i) paid (phase_closed closed i)
   (unique i) (noMove i) cut.before inside same hero first.trace.holes_sublist.subset
 have groupFixed:=no_push_unchanged group cut.beforeOutcomes quiet.1
 have otherInside : [other i]⊆group := by
  intro c member
  have eq:=List.mem_singleton.mp member
  subst c
  exact same.mem_iff.mpr (by simp [locks])
 have localOther:=LeftQuietIdentity11.subset_zero [other i] group cut.beforeOutcomes otherInside quiet.1
 have fixedOther : ownPushes [other i] (before++cut.beforeOutcomes)=0 := by
  rw [ownPushes_append,no_push_unchanged [other i] before stationary,stationary,localOther]
 have facts:=cut.before.logged.end_subset valid.1 group uniqueGroup inside
 have selected : locks i⊆endGroup group cut.beforeOutcomes := by rw [groupFixed];exact fun _ h=>same.mem_iff.mpr h
 have physical:=List.Subset.trans selected facts.2
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have sourceMember : source∈locks i := by rw [groupFixed] at owner;exact same.mem_iff.mp owner
 rcases head_shape i quiet.2 physical pays cut.headChecked metadata with south138|west137|east139
 ·obtain ⟨rfl,south⟩:=south138
  have checked : step soko1_1.board cut.middle .south=some cut.actor := by simpa only [south] using cut.headChecked
  have currentFirst:=first.append cut.before.logged
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 138 .south=[164] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 138 (.stay 164)) := by simpa only [headEq] using cut.headEffect
  have updated:=update_mono (locks i) (endGroup group cut.beforeOutcomes) (unique i) selected cut.headOutcome
  have shift : ∀i,LeftInwardPipe11.locks 0⊆update (locks i) (.push 138 (.stay 164)) := by decide +kernel
  have pipeLocks : LeftInwardPipe11.locks 0⊆Upper216Eight11.next cut := by
   change LeftInwardPipe11.locks 0⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
   rw [headEq] at updated ⊢
   exact List.Subset.trans (shift i) updated
  have pipeHero : cut.actor.state.player∈LeftInwardPipe11.region 0 := by
   rw [effect.2]
   exact LeftInwardPipe11.hero138
  have nextFacts:=Upper216Eight11.next_facts cut first.trace uniqueGroup inside bounded
  let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
    .cons cut.headChecked cut.headEffect (.nil _)
  let lead:=cut.before.logged.append one
  have afterReached:=first.trace.append lead.trace
  have ticket:=LeftInwardPipe11.future_four_with pipeClosed afterReached cut.after
    (Upper216Eight11.next cut) nextFacts.1 nextFacts.2.1 nextFacts.2.2 ⟨0,pipeHero,pipeLocks⟩
    (Upper216Eight11.tail_gone cut gone)
  have leadNN:=HeroLedger.Logged.energy_nonnegative lead (groupCertificate 18) valid group uniqueGroup inside bounded
  change 0≤energy state cut.actor.state group (cut.beforeOutcomes++[cut.headOutcome]) at leadNN
  have allShape : (cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes=outcomes := by
   simpa only [List.append_assoc,List.singleton_append] using cut.outcomesEq.symm
  have split:=energy_append state cut.actor.state final group (cut.beforeOutcomes++[cut.headOutcome]) cut.afterOutcomes
  rw [allShape,endGroup_append] at split
  change energy state final group outcomes=
    energy state cut.actor.state group (cut.beforeOutcomes++[cut.headOutcome])+
      energy cut.actor.state final (Upper216Eight11.next cut) cut.afterOutcomes at split
  omega
 ·obtain ⟨rfl,west⟩:=west137
  have isOther : other i=137 := by
   have checked : ∀i,(137:Cell)∈locks i→other i=137 := by decide +kernel
   exact checked i sourceMember
  have fixed137 : ownPushes [137] (before++cut.beforeOutcomes)=0 := by simpa only [isOther] using fixedOther
  have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
  let currentFirst:=first.append cut.before.logged
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)) := by simpa only [headEq] using cut.headEffect
  have two:=First137RestAnywhere11.rest_two currentFirst checked effect cut.after completed fixed137
  have allShape : (before++cut.beforeOutcomes)++.push 137 (.stay 136)::cut.afterOutcomes=before++outcomes := by
   calc
    _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by rw [headEq];simp only [List.append_assoc]
    _=before++outcomes := congrArg (fun rest=>before++rest) cut.outcomesEq.symm
  rw [allShape] at two
  omega
 ·obtain ⟨rfl,east⟩:=east139
  have isOther : other i=139 := by
   have checked : ∀i,(139:Cell)∈locks i→other i=139 := by decide +kernel
   exact checked i sourceMember
  have fixed139 : ownPushes [139] (before++cut.beforeOutcomes)=0 := by simpa only [isOther] using fixedOther
  have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [east] using cut.headChecked
  let currentFirst:=first.append cut.before.logged
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)) := by simpa only [headEq] using cut.headEffect
  have allShape : (before++cut.beforeOutcomes)++.push 139 (.stay 140)::cut.afterOutcomes=before++outcomes := by
   calc
    _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by rw [headEq];simp only [List.append_assoc]
    _=before++outcomes := congrArg (fun rest=>before++rest) cut.outcomesEq.symm
  have cap : energy soko1_1.initial final UpperBudget11.U6 ((before++cut.beforeOutcomes)++.push 139 (.stay 140)::cut.afterOutcomes)≤8 := by
   rw [allShape];exact upperCap
  exact False.elim (Gate139EastImpossible11.impossible currentFirst checked effect cut.after completed cap fixed139)
#print axioms noMove
#print axioms phase_closed
#print axioms head_shape
#print axioms future_four_with
end Owner1007.LeftInwardStart11
