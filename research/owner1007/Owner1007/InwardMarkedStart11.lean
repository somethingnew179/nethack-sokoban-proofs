import Owner1007.InwardMarkedStart11Geometry
import Owner1007.Inward213Pipe11
import Owner1007.Inward214Pipe11
import Owner1007.First137RestAnywhere11
import Owner1007.Gate139EastImpossible11
namespace Owner1007.InwardMarkedStart11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def index213 (i : Fin 8) : Fin 10:=if u i=187 then 0 else 5
def index214 (i : Fin 8) : Fin 8:=if u i=187 then 0 else 4
theorem impossible {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (prefixPair : 2≤energy soko1_1.initial state TightSplit11.A before)
 (i : Fin 8) (stationary : ownPushes [other i] before=0)
 (tag188 : endGroup [188] before=[u i]) (tag191 : endGroup [191] before=[189])
 (inside : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (locks i) outcomes=[]) : False:=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have good : OwnedCorral11.Good locks region state (locks i):=⟨i,hero,List.Subset.refl _⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged valid.1 (unique i) inside good first.trace.holes_sublist.subset gone
 have quiet:=LeftQuietIdentity11.quiet_zero_static (locks i) (region i) paid (phase_closed i)
  (unique i) (by intro hero member source owner dir adjacent;exact Or.inr trivial)
  cut.before inside (List.Perm.refl _) hero first.trace.holes_sublist.subset
 have fixed:=no_push_unchanged (locks i) cut.beforeOutcomes quiet.1
 let current:=first.append cut.before.logged
 have facts:=cut.before.logged.end_subset valid.1 (locks i) (unique i) inside
 have physical : locks i⊆cut.middle.boulders:=by simpa only [fixed] using facts.2
 have localOther:=LeftQuietIdentity11.subset_zero [other i] (locks i) cut.beforeOutcomes (by simp [locks]) quiet.1
 have fixedOther : ownPushes [other i] (before++cut.beforeOutcomes)=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ stationary,stationary,localOther]
 have fixedU:=no_push_unchanged [u i] cut.beforeOutcomes
  (LeftQuietIdentity11.subset_zero [u i] (locks i) cut.beforeOutcomes (by simp [locks]) quiet.1)
 have fixedRight:=no_push_unchanged [189] cut.beforeOutcomes
  (LeftQuietIdentity11.subset_zero [189] (locks i) cut.beforeOutcomes (by simp [locks]) quiet.1)
 have current188 : endGroup [188] (before++cut.beforeOutcomes)=[u i]:=by rw [endGroup_append,tag188,fixedU]
 have current191 : endGroup [191] (before++cut.beforeOutcomes)=[189]:=by rw [endGroup_append,tag191,fixedRight]
 have allEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by rw [List.append_assoc,←cut.outcomesEq]
 have currentUpper : energy soko1_1.initial final UpperBudget11.U6 ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)≤6:=by rw [allEffects];exact upperCap
 have currentRest : energy soko1_1.initial final UpperBudget11.Rest ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)<2:=by rw [allEffects];exact restCap
 obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
 have member : source∈locks i:=by rw [fixed] at owner;exact owner
 rcases head_shape i quiet.2 member physical cut.headChecked metadata with ⟨rfl,south⟩|⟨rfl,west⟩|⟨rfl,east⟩
 ·have checked : step soko1_1.board cut.middle .south=some cut.actor:=by simpa only [south] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 138 .south=[164] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 138 (.stay 164)):=by simpa only [headEq] using cut.headEffect
  let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome]:=.cons cut.headChecked cut.headEffect (.nil _)
  let extended:=current.append one
  have afterFacts:=Upper216Eight11.next_facts cut first.trace (unique i) inside (by change (locks i).length≤18;have size:(locks i).length=5:=rfl;omega)
  have afterGone:=Upper216Eight11.tail_gone cut gone
  have lifted:=update_mono (locks i) (endGroup (locks i) cut.beforeOutcomes) (unique i) (by rw [fixed];exact List.Subset.refl _) cut.headOutcome
  have after188 : endGroup [188] ((before++cut.beforeOutcomes)++[cut.headOutcome])=[u i]:=by
   rw [endGroup_append,current188,headEq]
   have different : u i≠138:=by unfold u;split <;> decide
   simp [endGroup,update,move,different,Ne.symm different,post]
  have after191 : endGroup [191] ((before++cut.beforeOutcomes)++[cut.headOutcome])=[189]:=by
   rw [endGroup_append,current191,headEq]
   simp [endGroup,update,move,post]
  have monoPair:=prefix_energy_le first (cut.before.logged.append one) TightSplit11.A (by decide) (by decide)
  have afterPair : 2≤energy soko1_1.initial cut.actor.state TightSplit11.A ((before++cut.beforeOutcomes)++[cut.headOutcome]):=by
   have same : before++(cut.beforeOutcomes++[cut.headOutcome])=(before++cut.beforeOutcomes)++[cut.headOutcome]:=by simp only [List.append_assoc]
   rw [same] at monoPair
   omega
  have sequence : ((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes=before++outcomes:=by
   simpa only [List.append_assoc,List.singleton_append] using allEffects
  have afterUpper : energy soko1_1.initial final UpperBudget11.U6 (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)≤6:=by rw [sequence];exact upperCap
  have markerOptions : marker i=213∨marker i=214:=by unfold marker;split <;> simp
  rcases markerOptions with is213|is214
  ·have small : Inward213Pipe11.locks (index213 i)⊆Upper216Eight11.next cut:=by
    change _⊆update (endGroup (locks i) cut.beforeOutcomes) cut.headOutcome
    rw [fixed,headEq]
    have bridge : ∀i,marker i=213→Inward213Pipe11.locks (index213 i)⊆update (locks i) (.push 138 (.stay 164)):=by decide +kernel
    exact bridge i is213
   have nextInside:=List.Subset.trans small afterFacts.2.1
   have nested:=cut.after.end_mono (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant extended.trace).1
    (Inward213Pipe11.locks (index213 i)) (Upper216Eight11.next cut) (Inward213Pipe11.unique _) nextInside small
   rw [afterGone] at nested
   have smallGone : endGroup (Inward213Pipe11.locks (index213 i)) cut.afterOutcomes=[]:=
    List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using nested h)
   have uSame : Inward213Pipe11.u (index213 i)=u i:=by
    have all : ∀i,Inward213Pipe11.u (index213 i)=u i:=by decide +kernel
    exact all i
   have nextHero : cut.actor.state.player∈Inward213Pipe11.region (index213 i):=by
    rw [effect.2]
    have all : ∀i,(138:Cell)∈Inward213Pipe11.region (index213 i):=by decide +kernel
    exact all i
   exact Inward213Pipe11.impossible extended cut.after afterUpper afterPair (index213 i)
    (by rw [uSame];exact after188) after191 nextInside nextHero smallGone
  ·have small : Inward214Pipe11.locks (index214 i)⊆Upper216Eight11.next cut:=by
    change _⊆update (endGroup (locks i) cut.beforeOutcomes) cut.headOutcome
    rw [fixed,headEq]
    have bridge : ∀i,marker i=214→Inward214Pipe11.locks (index214 i)⊆update (locks i) (.push 138 (.stay 164)):=by decide +kernel
    exact bridge i is214
   have nextInside:=List.Subset.trans small afterFacts.2.1
   have nested:=cut.after.end_mono (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant extended.trace).1
    (Inward214Pipe11.locks (index214 i)) (Upper216Eight11.next cut) (Inward214Pipe11.unique _) nextInside small
   rw [afterGone] at nested
   have smallGone : endGroup (Inward214Pipe11.locks (index214 i)) cut.afterOutcomes=[]:=
    List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using nested h)
   have uSame : Inward214Pipe11.u (index214 i)=u i:=by
    have all : ∀i,Inward214Pipe11.u (index214 i)=u i:=by decide +kernel
    exact all i
   have nextHero : cut.actor.state.player∈Inward214Pipe11.region (index214 i):=by
    rw [effect.2]
    have all : ∀i,(138:Cell)∈Inward214Pipe11.region (index214 i):=by decide +kernel
    exact all i
   exact Inward214Pipe11.impossible extended cut.after afterUpper afterPair (index214 i)
    (by rw [uSame];exact after188) after191 nextInside nextHero smallGone
 ·have otherEq : other i=137:=by
   have all : ∀i,(137:Cell)∈locks i→other i=137:=by decide +kernel
   exact all i member
  have fixed137 : ownPushes [137] (before++cut.beforeOutcomes)=0:=by simpa only [otherEq] using fixedOther
  have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)):=by simpa only [headEq] using cut.headEffect
  have two:=First137RestAnywhere11.rest_two current checked effect cut.after completed fixed137
  rw [headEq] at currentRest
  omega
 ·have otherEq : other i=139:=by
   have all : ∀i,(139:Cell)∈locks i→other i=139:=by decide +kernel
   exact all i member
  have fixed139 : ownPushes [139] (before++cut.beforeOutcomes)=0:=by simpa only [otherEq] using fixedOther
  have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)):=by simpa only [headEq] using cut.headEffect
  rw [headEq] at currentUpper
  exact Gate139EastImpossible11.impossible current checked effect cut.after completed (by omega) fixed139
#print axioms impossible
end Owner1007.InwardMarkedStart11
