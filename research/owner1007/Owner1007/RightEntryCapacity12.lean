import Owner1007.RightCapacity12
import Owner1007.TwoReserves12
namespace Owner1007.RightEntryCapacity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev R := RightEnergy12.Right
abbrev P := RightPrice4.P
abbrev Q := RightCapacity12.Q
abbrev A : List Cell := [141,168]

theorem final_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) : final.boulders.length=2 := by
 have conserved := (reached.append logged.trace).conservation
 have empty : final.holes=[] := completed
 change 20+final.holes.length=final.boulders.length+18 at conserved
 rw [empty] at conserved
 simp only [List.length_nil] at conserved
 omega

theorem consumed_bound {n : Nat} {K D : Fin n → List Cell} {C : Fin n → Int}
 (closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p K D C)
 (uniqueK : ∀ i, (K i).Nodup) (terminal : ∀ i, K i=[] → C i=0)
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin n} (hero : state.player∈D i) (inside : K i⊆group)
 (gone : endGroup group outcomes=[]) : C i≤energy p group outcomes := by
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed uniqueK
   logged reached group unique subset hero inside
 have empty : K j=[] := by
   apply List.eq_nil_iff_forall_not_mem.mpr
   intro c member
   have found := kept member
   simpa only [gone,List.not_mem_nil] using found
 have zero := terminal j empty
 rw [zero] at price
 simpa only [energy,gone,debtOf,weightSum,Int.add_zero] using price

theorem upper_consumed_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders)
 (gone : endGroup A outcomes=[]) : 2≤energy p A outcomes := by
 have closed := PricedCorral.closed_of_check _ _ _ _ _ _ RightCapacity12.upperMatrix
 exact consumed_bound closed (by decide +kernel) (by decide +kernel) logged reached A
   (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   (i:=0) (by rw [player]; decide +kernel) (by decide +kernel) gone

theorem low_consumed_three {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders)
 (gone : endGroup [246] outcomes=[]) : 3≤energy p [246] outcomes := by
 have closed := PricedCorral.closed_of_check _ _ _ _ _ _ RightCapacity12.lowMatrix
 exact consumed_bound closed (by decide +kernel) (by decide +kernel) logged reached [246]
   (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   (i:=0) (by rw [player]; decide +kernel) (by decide +kernel) gone

theorem upper_one {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders)
 (small : (endGroup A outcomes).length≤1) : 1≤energy p A outcomes := by
 have closed := PricedCorral.closed_of_check _ _ _ _ _ _ RightCapacity12.upperMatrix
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed (by decide +kernel)
   logged reached A (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   (i:=0) (by rw [player]; decide +kernel) (by decide +kernel)
 have nonzero : j.val≠0 := by
   intro zero
   have actualJ : j=0 := Fin.ext zero
   subst j
   have count := List.Nodup.length_le_of_subset (show (RightCapacity12.upperLocks 0).Nodup by decide +kernel) kept
   change 2≤(endGroup A outcomes).length at count
   omega
 have credit : ∀ j : Fin 5, j.val≠0 → RightCapacity12.upperCredit j≤1 := by decide +kernel
 have cheap := credit j nonzero
 change 2≤ownSlack p A outcomes+RightCapacity12.upperCredit j at price
 have nn := NonlinearFacts.weightSum_nonnegative (fun c=>-p.boulder c) (endGroup A outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c≤0 at h; omega)
 change 0≤debtOf p (endGroup A outcomes) at nn
 unfold energy
 omega

theorem p_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders) (completed : Goal final) :
 2≤energy p P outcomes := by
 have bound := RightEnergy12.raw_group_energy logged reached P (by decide +kernel)
   (List.Subset.trans (by decide +kernel) inside) completed
 have bonus : RightEnergy12.cert.bonus state.player (NetHack.Sokoban.PatternCorrection.project P)=2 := by
   rw [player]
   decide +kernel
 rw [bonus] at bound
 exact bound

theorem q_splits {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (unique : state.boulders.Nodup) (inside : R⊆state.boulders) :
 energy p Q outcomes=energy p A outcomes+energy p [246] outcomes+energy p [271] outcomes ∧
 energy p R outcomes=energy p P outcomes+energy p Q outcomes := by
 have a := logged.energy_split unique p A [246,271] (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
 have b := logged.energy_split unique p [246] [271] (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
 have c := logged.energy_split unique p P Q (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
 have same := energy_perm p (show (P++Q).Perm R by decide +kernel) outcomes
 change energy p Q outcomes=energy p A outcomes+energy p [246,271] outcomes at a
 change energy p [246,271] outcomes=energy p [246] outcomes+energy p [271] outcomes at b
 exact ⟨by omega,by omega⟩

theorem five_of_both {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders) (completed : Goal final)
 (low : 1≤energy p [246] outcomes) (token : 1≤energy p [271] outcomes) :
 5≤energy p R outcomes := by
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

theorem five_of_dead271 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : R⊆state.boulders) (completed : Goal final)
 (survives : endGroup [271] outcomes≠[]) (token : 1≤energy p [271] outcomes) :
 5≤energy p R outcomes := by
 have unique := reached.boulders_nodup (by decide +kernel)
 have splits := q_splits logged unique inside
 have reserve := p_two logged reached player inside completed
 have nnu := logged.energy_nonnegative Generated.soko1_2_potential_valid A
 have nnl := logged.energy_nonnegative Generated.soko1_2_potential_valid [246]
 change 0≤energy p A outcomes at nnu
 change 0≤energy p [246] outcomes at nnl
 by_cases lowGone : endGroup [246] outcomes=[]
 · have three := low_consumed_three logged reached player inside lowGone
   omega
 · have a := logged.end_split unique A [246,271] (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   have b := logged.end_split unique [246] [271] (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   have all := logged.end_subset unique (A++[246,271]) (by decide +kernel) (List.Subset.trans (by decide +kernel) inside)
   have count := List.Nodup.length_le_of_subset all.1 all.2
   rw [final_two logged reached completed] at count
   have la := a.length_eq
   have lb := b.length_eq
   simp only [List.length_append] at la lb
   change (endGroup A outcomes).length+(endGroup [246,271] outcomes).length=(endGroup (A++[246,271]) outcomes).length at la
   change (endGroup [246] outcomes).length+(endGroup [271] outcomes).length=(endGroup [246,271] outcomes).length at lb
   have lpos : 1≤(endGroup [246] outcomes).length := by cases h:endGroup [246] outcomes with | nil => exact False.elim (lowGone h) | cons c rest => simp
   have tpos : 1≤(endGroup [271] outcomes).length := by cases h:endGroup [271] outcomes with | nil => exact False.elim (survives h) | cons c rest => simp
   have gone : endGroup A outcomes=[] := List.eq_nil_of_length_eq_zero (by omega)
   have two := upper_consumed_two logged reached player inside gone
   omega
#print axioms upper_one
#print axioms five_of_both
#print axioms five_of_dead271
end Owner1007.RightEntryCapacity12

