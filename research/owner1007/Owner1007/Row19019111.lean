import Owner1007.TightTailConsumed11
import Owner1007.GrowingCorral11
import Owner1007.LeftQuietIdentity11
import Owner1007.UpperShaftGate11
namespace Owner1007.Row19019111
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11
def locks (_ : Fin 1) : List Cell := [190,191]
-- The fixed 72-cell floor component below the occupied entrance 190.
-- Other boulders and holes are universally quantified by closed.
def region (_ : Fin 1) : List Cell := [183,184,185,186,187,188,189,192,193,194,209,210,211,212,213,214,215,216,217,218,219,220,239,262,263,264,265,266,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
def paid (source : Cell) (dir : Dir) : Prop := source=190∧dir=.north
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem matrix : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor := by dsimp only [region];decide +kernel
theorem unique (i : Fin 1) : (locks i).Nodup := by dsimp only [locks];decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor (fun _=>matrix)
theorem growth : ∀i source dir j dest,source∈locks i→dest∈pushTargets soko1_1.board source dir→
 locks j⊆dest::(locks i).erase source→region j⊆region i++locks i := by
 intro i source dir j dest member target next c found
 exact List.mem_append_left _ found
theorem hero189 : (189:Cell)∈region 0 := by decide +kernel
theorem outside : ∀c,c∈([137,139] : List Cell)→c∉region 0 := by decide +kernel

theorem excluded {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (tail : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+pushes≤325)
 (fixed137 : ownPushes [137] before=0) (fixed139 : ownPushes [139] before=0)
 (inside : [190,191]⊆state.boulders) (hero : state.player∈region 0) : False := by
 let full := first.append tail
 obtain ⟨_,upper,left,rest⟩ := Tight32511.budgets full completed cheap
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have tag137 := no_push_unchanged [137] before fixed137
 have tag139 := no_push_unchanged [139] before fixed139
 have physical137 : 137∈state.boulders := (first.end_subset (by decide) [137] (by decide) (by decide)).2 (by rw [tag137];simp)
 have physical139 : 139∈state.boulders := (first.end_subset (by decide) [139] (by decide) (by decide)).2 (by rw [tag139];simp)
 have selectedInside : ([190,191]++[137,139] : List Cell)⊆state.boulders := by
  apply List.append_subset.mpr
  refine ⟨inside,?_⟩
  intro c member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  ·exact physical137
  ·exact physical139
 have gone := TightTailConsumed11.gone first tail completed cheap [190,191] (by decide) inside
 have good : OwnedCorral11.Good locks region state [190,191] := ⟨0,hero,List.Subset.refl _⟩
 obtain ⟨cut⟩ := Upper216Eight11.first_any closed unique (by decide) tail valid.1
   (by decide) inside good first.trace.holes_sublist.subset gone
 have sep : GrowingCorral11.Separated locks region state [190,191] [137,139] :=
   ⟨0,hero,List.Subset.refl _,outside⟩
 have noGate := (GrowingCorral11.Quiet.separated_untouched closed unique growth cut.before valid.1
   (by decide) selectedInside sep first.trace.holes_sublist.subset).2
 have local137 := LeftQuietIdentity11.subset_zero [137] [137,139] cut.beforeOutcomes (by decide) noGate
 have local139 := LeftQuietIdentity11.subset_zero [139] [137,139] cut.beforeOutcomes (by decide) noGate
 have whole137 : ownPushes [137] (before++cut.beforeOutcomes)=0 := by rw [ownPushes_append,tag137,fixed137,local137]
 have whole139 : ownPushes [139] (before++cut.beforeOutcomes)=0 := by rw [ownPushes_append,tag139,fixed139,local139]
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 rcases pays with ⟨rfl,north⟩
 let current := first.append cut.before.logged
 have checked : step soko1_1.board cut.middle .north=some cut.actor := by simpa only [north] using cut.headChecked
 have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 190 .north=[164] from by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 190 (.stay 164)) := by simpa only [headEq] using cut.headEffect
 have eqEffects : (before++cut.beforeOutcomes)++.push 190 (.stay 164)::cut.afterOutcomes=before++outcomes := by
  calc
   _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by rw [headEq];simp only [List.append_assoc]
   _=before++outcomes := congrArg (fun middle=>before++middle) cut.outcomesEq.symm
 have upperCheap : energy soko1_1.initial final U6 ((before++cut.beforeOutcomes)++.push 190 (.stay 164)::cut.afterOutcomes)<8 := by rw [eqEffects];omega
 have restCheap : energy soko1_1.initial final Rest ((before++cut.beforeOutcomes)++.push 190 (.stay 164)::cut.afterOutcomes)<2 := by rw [eqEffects];omega
 rcases UpperShaftGate11.gate_moved_before_north current checked effect cut.after completed upperCheap restCheap with moved|moved
 ·omega
 ·omega
#print axioms matrix
#print axioms excluded
end Owner1007.Row19019111
