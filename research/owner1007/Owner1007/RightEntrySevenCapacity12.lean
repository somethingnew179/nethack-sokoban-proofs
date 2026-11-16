import Owner1007.RightEntryBound12
namespace Owner1007.RightEntrySevenCapacity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.RightEntryCapacity12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem seven_of_both_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders) (completed : Goal final)
 (low : 2≤energy p [246] outcomes) (token : 2≤energy p [271] outcomes) :
 7≤energy p R outcomes := by
 have unique := reached.boulders_nodup (by decide +kernel)
 have splits := q_splits logged unique inside
 have reserve := p_two logged reached player inside completed
 have nnu := logged.energy_nonnegative Generated.soko1_2_potential_valid A
 have nnt := logged.energy_nonnegative Generated.soko1_2_potential_valid [271]
 change 0≤energy p A outcomes at nnu
 change 0≤energy p [271] outcomes at nnt
 by_cases small : (endGroup A outcomes).length≤1
 · have one := upper_one logged reached player inside small
   omega
 · have split := logged.end_split unique A [246] (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   have all := logged.end_subset unique (A++[246]) (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   have count := List.Nodup.length_le_of_subset all.1 all.2
   rw [final_two logged reached completed] at count
   have lengths := split.length_eq
   simp only [List.length_append] at lengths
   have gone : endGroup [246] outcomes=[] := List.eq_nil_of_length_eq_zero (by omega)
   have three := low_consumed_three logged reached player inside gone
   omega


theorem token_consumed_one {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders)
 (gone : endGroup [271] outcomes=[]) : 1≤energy p [271] outcomes := by
 have closed := PricedCorral.closed_of_check _ _ _ _ _ _ RightCapacity12.tokenMatrix
 exact consumed_bound closed (by decide +kernel) (by decide +kernel) logged reached [271]
   (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   (i:=0) (by rw [player]; decide +kernel) (by decide +kernel) gone


theorem low_at194_slack_two {state middle dirs pushes moves before}
 (logged : Logged soko1_2.board state dirs middle pushes moves before)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders)
 (at194 : endGroup [246] before=[194]) : 2≤ownSlack p [246] before := by
 have closed:=PricedCorral.closed_of_check _ _ _ _ _ _ RightCapacity12.lowMatrix
 obtain ⟨j,_,kept,price⟩:=RightPrice4.owned_trace_price closed (by decide +kernel)
   logged reached [246] (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   (i:=0) (by rw[player];decide +kernel) (by decide +kernel)
 rw[at194] at kept
 have credit:∀ j:Fin 5,RightCapacity12.lowLocks j⊆[194]→RightCapacity12.lowCredit j≤1:=by decide +kernel
 have upper:=credit j kept
 change 3≤ownSlack p [246] before+RightCapacity12.lowCredit j at price
 omega

theorem eight_of_pair {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir}{past pastMoves:Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player:state.player=296) (inside:(R++[270])⊆state.boulders) (completed:Goal final)
 (pair : 2≤(endGroup [218,270] outcomes).length) : 8≤energy p R outcomes := by
 have unique:=reached.boulders_nodup (by decide +kernel)
 have rightInside:=List.Subset.trans (show R⊆R++[270] from fun _ h=>List.mem_append_left _ h) inside
 have split:=logged.end_split unique [218,270] Q (by decide +kernel)
   (List.Subset.trans (by decide +kernel) inside)
 have actual:=logged.end_subset unique ([218,270]++Q) (by decide +kernel)
   (List.Subset.trans (by decide +kernel) inside)
 have count:=List.Nodup.length_le_of_subset actual.1 actual.2
 rw[final_two logged reached completed] at count
 have lengths:=split.length_eq
 simp only[List.length_append] at lengths
 have goneQ:endGroup Q outcomes=[]:=List.eq_nil_of_length_eq_zero (by omega)
 have splitA:=logged.end_split unique A [246,271] (by decide +kernel)
   (List.Subset.trans (by decide +kernel) rightInside)
 have splitL:=logged.end_split unique [246] [271] (by decide +kernel)
   (List.Subset.trans (by decide +kernel) rightInside)
 have sameA:endGroup (A++[246,271]) outcomes=[]:=by exact goneQ
 have la:=splitA.length_eq
 have lb:=splitL.length_eq
 rw[sameA] at la
 simp only[List.length_append,List.length_nil] at la lb
 change (endGroup A outcomes).length+(endGroup [246,271] outcomes).length=0 at la
 change (endGroup [246] outcomes).length+(endGroup [271] outcomes).length=(endGroup [246,271] outcomes).length at lb
 have aGone:endGroup A outcomes=[]:=List.eq_nil_of_length_eq_zero (by omega)
 have lGone:endGroup [246] outcomes=[]:=List.eq_nil_of_length_eq_zero (by omega)
 have tGone:endGroup [271] outcomes=[]:=List.eq_nil_of_length_eq_zero (by omega)
 have ea:=upper_consumed_two logged reached player rightInside aGone
 have el:=low_consumed_three logged reached player rightInside lGone
 have et:=token_consumed_one logged reached player rightInside tGone
 have ep:=p_two logged reached player rightInside completed
 have splitE:=q_splits logged unique rightInside
 omega
#print axioms seven_of_both_two
#print axioms low_at194_slack_two
#print axioms eight_of_pair
end Owner1007.RightEntrySevenCapacity12
