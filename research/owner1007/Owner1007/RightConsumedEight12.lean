import Owner1007.RightCapacity12
import Owner1007.EndGroupMono
namespace Owner1007.RightConsumedEight12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
abbrev R := RightEnergy12.Right

theorem right_eight {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
 (completed : Goal final) (gone : endGroup R outcomes=[]) :
 8≤energy p R outcomes := by
 have unique : soko1_2.initial.boulders.Nodup := by decide +kernel
 have goneSmall (small : List Cell) (uniqueSmall : small.Nodup) (inside : small⊆soko1_2.initial.boulders)
     (subset : small⊆R) : endGroup small outcomes=[] := by
   have member := logged.end_mono unique small R uniqueSmall inside subset
   rw [gone] at member
   exact List.eq_nil_of_subset_nil member
 have upperGone := goneSmall [141,168] (by decide) (by decide) (by decide)
 have lowGone := goneSmall [246] (by decide) (by decide) (by decide)
 have tokenGone := goneSmall [271] (by decide) (by decide) (by decide)
 have upper := RightCapacity12.upper_consumed_two logged upperGone
 have low := RightCapacity12.low_consumed_three logged lowGone
 have token := RightCapacity12.token_consumed_one logged tokenGone
 have reserve := RightPrice4.p_energy_two logged completed
 have a := logged.energy_split unique p [141,168] [246,271] (by decide) (by decide)
 have b := logged.energy_split unique p [246] [271] (by decide) (by decide)
 have c := logged.energy_split unique p [192,193,218] [141,168,246,271] (by decide) (by decide)
 have perm : ([192,193,218]++[141,168,246,271]).Perm R := by decide +kernel
 have same := energy_perm p perm outcomes
 change 2≤energy p [141,168] outcomes at upper
 change 3≤energy p [246] outcomes at low
 change 1≤energy p [271] outcomes at token
 change 2≤energy p [192,193,218] outcomes at reserve
 simp only [List.cons_append,List.nil_append] at a b c same
 omega

theorem right_gone_of_two_survive {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
 (completed : Goal final) (a b : Cell) (distinct : a≠b)
 (inside : [a,b]⊆soko1_2.initial.boulders) (away : a∉R ∧ b∉R)
 (first : endGroup [a] outcomes≠[]) (second : endGroup [b] outcomes≠[]) :
 endGroup R outcomes=[] := by
 have unique : soko1_2.initial.boulders.Nodup := by decide +kernel
 have pairUnique : ([a,b] : List Cell).Nodup := by simp [distinct]
 have bothUnique : ([a,b]++R).Nodup := by
   apply List.nodup_append.mpr
   refine ⟨pairUnique,by decide,?_⟩
   intro c before d after equal
   rcases List.mem_cons.mp before with rfl|later
   · subst d
     exact away.1 after
   · have same : c=b := List.mem_singleton.mp later
     subst c
     subst d
     exact away.2 after
 have bothInside : [a,b]++R⊆soko1_2.initial.boulders := by
   intro c member
   rcases List.mem_append.mp member with h|h
   · exact inside h
   · exact (show R⊆soko1_2.initial.boulders by decide) h
 have pairSplit := logged.end_split unique [a] [b] pairUnique inside
 have pairCount := pairSplit.length_eq
 have bothSplit := logged.end_split unique [a,b] R bothUnique bothInside
 have bothCount := bothSplit.length_eq
 have finalInside := logged.end_subset unique ([a,b]++R) bothUnique bothInside
 have bound := List.Nodup.length_le_of_subset finalInside.1 finalInside.2
 have firstPos : 1≤(endGroup [a] outcomes).length := List.length_pos_iff.mpr first
 have secondPos : 1≤(endGroup [b] outcomes).length := List.length_pos_iff.mpr second
 have conserved := logged.trace.conservation
 have empty : final.holes=[] := completed
 change 20+final.holes.length=final.boulders.length+18 at conserved
 rw [empty] at conserved
 simp only [List.cons_append,List.nil_append,List.length_append,List.length_nil] at pairCount bothCount conserved
 simp only [List.cons_append,List.nil_append] at bound
 exact List.eq_nil_of_length_eq_zero (by omega)
#print axioms right_eight
#print axioms right_gone_of_two_survive
end Owner1007.RightConsumedEight12
