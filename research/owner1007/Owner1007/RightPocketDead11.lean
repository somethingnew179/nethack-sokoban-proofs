import Owner1007.RightTripleEight11
namespace Owner1007.RightPocketDead11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Five hand-written footprints. The last drops191 after its West push:
-- the two remaining stones193/219 alone seal the194/220 support pocket.
def locks (i : Fin 5) : List Cell := match i.val with
 |0=>[191,193,216]
 |1=>[191,193,217]
 |2=>[191,193,218]
 |3=>[191,193,219]
 |_=>[193,219]
def region (i : Fin 5) : List Cell := PostCuts11.without PostCuts11.H (match i.val with
 |0=>[191,192,193,194,216,217,218,219,220]
 |1=>[191,192,193,194,217,218,219,220]
 |2=>[191,192,193,194,218,219,220]
 |3=>[191,193,194,219,220]
 |_=>[193,194,219,220])
def paid (source : Cell) (dir : Dir) : Prop := (source=191∨source=193∨source=219)∧dir=.east
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true := by decide +kernel
theorem node3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 3=true := by decide +kernel
theorem node4 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 4=true := by decide +kernel
theorem floor (i : Fin 5) : region i⊆soko1_1.board.floor := by
 have row : (List.finRange 5).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c member)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem mate193 : ∀i,(193:Cell)∈locks i := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩ := i
 have cases : i=0∨i=1∨i=2∨i=3∨i=4 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl
 · exact node0
 · exact node1
 · exact node2
 · exact node3
 · exact node4

/-- With player outside the pocket, these three selected stones cannot
all disappear. This is an actual legal-trace obstruction, not an energy bound. -/
theorem impossible_gone {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (gUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (hero : state.player∈region 0) (selected : locks 0⊆group) (gone : endGroup group outcomes=[]) : False := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good : OwnedCorral11.Good locks region state group := ⟨0,hero,selected⟩
 obtain ⟨cut⟩ := Upper216Eight11.first_any closed unique nonempty logged valid.1 gUnique inside good reached.holes_sublist.subset gone
 obtain ⟨i,heroBefore,locksBefore⟩ := Upper216Eight11.quiet_good_any closed unique cut.before
   valid.1 gUnique inside good reached.holes_sublist.subset
 have beforeFacts := cut.before.logged.end_subset valid.1 group gUnique inside
 have beforeReached := reached.append cut.before.logged.trace
 have nextFacts := Upper216Eight11.next_facts cut reached gUnique inside bounded
 have nextReached := beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have nextGone := Upper216Eight11.tail_gone cut gone
 obtain ⟨source,owner,metadata,sources,east⟩ := cut.headPaid
 have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [east] using cut.headChecked
 rcases sources with rfl|rfl|rfl
 · have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 191 .east=[192] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have pairBefore : [191,193]⊆endGroup group cut.beforeOutcomes := by
     intro c member
     rcases List.mem_cons.mp member with rfl|later
     · exact owner
     · have eq : c=193 := List.mem_singleton.mp later
       subst c
       exact locksBefore (mate193 i)
   have transport := update_mono [191,193] (endGroup group cut.beforeOutcomes) (by decide) pairBefore cut.headOutcome
   have pair : [192,193]⊆Upper216Eight11.next cut := by
     change [192,193]⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
     rw [headEq] at transport ⊢
     exact List.Subset.trans (by decide) transport
   exact Upper216Eight11.frozen_absurd cut.after
     (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1 nextFacts.1 nextFacts.2.1
     (Owner1007.locked_of_check _ [192,193] (by decide +kernel)) (List.Subset.trans pair nextFacts.2.1)
     (show 192∈[192,193] by decide) (pair (by decide)) nextGone
 · have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 193 .east=[194] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have owned : 194∈Upper216Eight11.next cut := by
     change 194∈update (endGroup group cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     simp only [update,move,if_pos owner,post,List.mem_cons]
     exact Or.inl trivial
   exact Upper216Eight11.frozen_absurd cut.after
     (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1 nextFacts.1 nextFacts.2.1
     (Owner1007.locked_of_check _ [194] (by decide +kernel)) (by simpa using nextFacts.2.1 owned)
     (show 194∈[194] by decide) owned nextGone
 · have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 219 .east=[220] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have owned : 220∈Upper216Eight11.next cut := by
     change 220∈update (endGroup group cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     simp only [update,move,if_pos owner,post,List.mem_cons]
     exact Or.inl trivial
   exact Upper216Eight11.frozen_absurd cut.after
     (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1 nextFacts.1 nextFacts.2.1
     (Owner1007.locked_of_check _ [220] (by decide +kernel)) (by simpa using nextFacts.2.1 owned)
     (show 220∈[220] by decide) owned nextGone
#print axioms node0
#print axioms node1
#print axioms node2
#print axioms node3
#print axioms node4
#print axioms impossible_gone
end Owner1007.RightPocketDead11
