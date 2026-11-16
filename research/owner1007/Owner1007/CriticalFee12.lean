import Owner1007.OwnedEventsMore12
namespace Owner1007.CriticalFee12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential
def A : Outcome := .push 238 (.stay 264)
def B : Outcome := .push 264 (.stay 290)
def hit (needle outcome : Outcome) : Nat := if outcome=needle then 1 else 0
def fee (outcome : Outcome) : Int := 2*Int.ofNat (hit A outcome)+4*Int.ofNat (hit B outcome)
def residue (outcome : Outcome) : Int := slack p outcome-fee outcome
def count (needle : Outcome) (group : List Cell) : List Outcome→Nat
 | []=>0
 | outcome::rest=>hit needle (projectedOutcome group outcome)+count needle (update group outcome) rest
def residual (group : List Cell) : List Outcome→Int
 | []=>0
 | outcome::rest=>residue (projectedOutcome group outcome)+residual (update group outcome) rest

theorem residue_nonnegative {state dir t outcome}
 (checked : step soko1_2.board state dir=some t) (effect : Matches state t outcome)
 (group : List Cell) :0≤residue (projectedOutcome group outcome) := by
 by_cases a : projectedOutcome group outcome=A
 · rw [a];decide +kernel
 · by_cases b : projectedOutcome group outcome=B
   · rw [b];decide +kernel
   · have nn := projected_slack_nonnegative p group outcome
       (logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect)
     have zeroFee : fee (projectedOutcome group outcome)=0 := by
       simp only [fee,hit,if_neg a,if_neg b]
       decide +kernel
     unfold residue
     rw [zeroFee,Int.sub_zero]
     exact nn

theorem residual_nonnegative {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (group : List Cell) :0≤residual group outcomes := by
 induction logged generalizing group with
 |nil=>exact Int.le_refl 0
 |@cons state dir t rest final pushes moves outcome outcomes checked effect tail ih=>
   have one := residue_nonnegative checked effect group
   have later := ih (update group outcome)
   change 0≤residue (projectedOutcome group outcome)+residual (update group outcome) outcomes
   omega

theorem count_append (needle : Outcome) (group : List Cell) (first second : List Outcome) :
 count needle group (first++second)=count needle group first+count needle (endGroup group first) second := by
 induction first generalizing group with
 |nil=>simp only [List.nil_append,count,endGroup,Nat.zero_add]
 |cons outcome rest ih=>
   simp only [List.cons_append,count,endGroup,ih,Nat.add_assoc]

theorem residual_append (group : List Cell) (first second : List Outcome) :
 residual group (first++second)=residual group first+residual (endGroup group first) second := by
 induction first generalizing group with
 |nil=>simp only [List.nil_append,residual,endGroup,Int.zero_add]
 |cons outcome rest ih=>
   simp only [List.cons_append,residual,endGroup,ih,Int.add_assoc]

theorem ledger (group : List Cell) (outcomes : List Outcome) :
 ownSlack p group outcomes=residual group outcomes+2*Int.ofNat (count A group outcomes)+4*Int.ofNat (count B group outcomes) := by
 induction outcomes generalizing group with
 |nil=>rfl
 |cons outcome rest ih=>
   have later := ih (update group outcome)
   simp only [ownSlack,residual,count,Int.ofNat_eq_natCast,Int.natCast_add] at *
   unfold residue fee
   simp only [Int.ofNat_eq_natCast]
   omega

theorem event_count (needle : Outcome) (group : List Cell) (before : List Outcome) (head : Outcome) (after : List Outcome)
 (same : projectedOutcome (endGroup group before) head=needle) :1≤count needle group (before++head::after) := by
 rw [count_append]
 have selfHit : hit needle needle=1 := by simp [hit]
 simp only [count,same,selfHit]
 omega

theorem event_residual_le {state middle next final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_2.board next afterDirs final afterPushes afterMoves after)
 (group : List Cell) (head : Outcome) :
 residue (projectedOutcome (endGroup group before) head)≤residual group (before++head::after) := by
 have prefixNN := residual_nonnegative first group
 have laterNN := residual_nonnegative last (update (endGroup group before) head)
 rw [residual_append]
 simp only [residual]
 omega

theorem residue_other {source ending} (a : source≠238) (b : source≠264) :
 residue (.push source ending)=slack p (.push source ending) := by
 have noA : (.push source ending : Outcome)≠A := by
   intro same
   exact a (Outcome.push.inj same).1
 have noB : (.push source ending : Outcome)≠B := by
   intro same
   exact b (Outcome.push.inj same).1
 have zeroFee : fee (.push source ending)=0 := by
   simp only [fee,hit,if_neg noA,if_neg noB]
   decide +kernel
 unfold residue
 rw [zeroFee,Int.sub_zero]

theorem energy_eight (group : List Cell) (outcomes : List Outcome)
 (a : 1≤count A group outcomes) (b : 1≤count B group outcomes)
 (other : 2≤residual group outcomes) :8≤energy p group outcomes := by
 have exactLedger := ledger group outcomes
 have debt := NonlinearFacts.weightSum_nonnegative (fun c=>-p.boulder c) (endGroup group outcomes)
   (fun c=>by have valid:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at valid;omega)
 change 0≤debtOf p (endGroup group outcomes) at debt
 simp only [Int.ofNat_eq_natCast] at exactLedger
 unfold energy
 omega
#print axioms ledger
#print axioms event_count
#print axioms event_residual_le
#print axioms residue_other
#print axioms energy_eight
end Owner1007.CriticalFee12
