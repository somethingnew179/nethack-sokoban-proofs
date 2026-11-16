import Owner1007.NorthPrepared12
import Owner1007.NorthBudget22312
import Owner1007.AfterJBound12
import Owner1007.North265Bound12
import Owner1007.North318Bound12
import Owner1007.Final224
namespace Owner1007.NorthForcedRing12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential

theorem exclude_strong {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤223)
 (branch : 6≤energy p NorthBound12.G outcomes ∨
   (5≤energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes≠[])) : False := by
 have whole := NorthWrap12.canonical_north logged
 have right := RightPrice4.right_energy_four whole completed
 have capacity := fun survives => RightCapacity12.right_energy_five_of318survives whole completed survives
 have perm : (update Final222.G (.push 371 (.stay 345))).Perm NorthBound12.G := by decide +kernel
 have same : energy p Final222.G (.walk 397 :: .push 371 (.stay 345) :: outcomes) =
     energy p NorthBound12.G outcomes :=
   (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
 have canonical : 6≤energy p Final222.G (.walk 397 :: .push 371 (.stay 345) :: outcomes) ∨
   (5≤energy p Final222.G (.walk 397 :: .push 371 (.stay 345) :: outcomes) ∧
    endGroup [318] (.walk 397 :: .push 371 (.stay 345) :: outcomes)≠[]) := by
   rcases branch with six | ⟨five,survives⟩
   · exact Or.inl (by rw [same]; exact six)
   · refine Or.inr ⟨by rw [same]; exact five,?_⟩
     change endGroup (update [318] (.push 371 (.stay 345))) outcomes≠[]
     have unchanged : update [318] (.push 371 (.stay 345))=[318] := by decide +kernel
     rw [unchanged]
     exact survives
 have bound := Final224.conditional_224 whole completed right capacity canonical
 omega

theorem forced_ring {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤223) :
 ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
 ∃ i : Fin 10,
 outcomes=before ++ .push 291 (.stay 290)::after ∧
 Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle .west=some t ∧ Matches middle t (.push 291 (.stay 290)) ∧
 Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
 middle.player∈PreCage12.northRegion i ∧ PreCage12.northLocks i⊆endGroup NorthTagFacts12.selected before ∧
 endGroup [213] before=[PreCage12.northS i] ∧ endGroup [345] before=[291] ∧
 PreCage12.northTag i=291 ∧
 (∀ small : List Cell, small⊆NorthTagFacts12.fixed → endGroup small before=small) := by
 have budget := NorthBudget22312.budget logged completed cheap
 obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,source,ending,after,
   afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,hero,locks,sourceMember,owner,pays,sAt,tAt,unchanged⟩ :=
   NorthPrepared12.prepared logged completed budget.1 budget.2.1
 have oldLocks := NorthPrepared12.g_end_subset first i tAt unchanged
 have fixedOld : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before=small := by
   intro small subset
   exact unchanged small (List.Subset.trans subset (show NorthEvents12.J⊆NorthTagFacts12.fixed by decide +kernel))
 have reached := NorthBound12.north_reached.append first.trace
 rcases pays with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   exact False.elim (exclude_strong logged completed cheap
     (AfterJBound12.firstJ_cases logged completed 0 shape first checked effect last
       (NorthPrepared12.oldIndex i) oldLocks fixedOld))
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 238 .south=[264] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   exact False.elim (exclude_strong logged completed cheap
     (AfterJBound12.firstJ_cases logged completed 1 shape first checked effect last
       (NorthPrepared12.oldIndex i) oldLocks fixedOld))
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   exact False.elim (exclude_strong logged completed cheap
     (North265Bound12.first265_cases logged completed shape first checked effect last
       (NorthPrepared12.oldIndex i) oldLocks fixedOld))
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   have branch := North318Bound12.first318_cases logged shape first checked effect last
     (NorthPrepared12.oldIndex i) (NorthPrepared12.old_region i hero) oldLocks fixedOld
   exact False.elim (exclude_strong logged completed cheap (Or.inr branch))
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     NorthEvents12.ring_activation (by decide +kernel) checked effect
   subst ending
   have current : PreCage12.northTag i=291 := by
     have table : ∀ i, 291∈PreCage12.northLocks i → PreCage12.northTag i=291 := by decide +kernel
     exact table i sourceMember
   rw [current] at tAt
   exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,t,after,afterDirs,afterPushes,afterMoves,
     i,shape,first,checked,effect,last,hero,locks,sAt,tAt,current,unchanged⟩
#print axioms exclude_strong
#print axioms forced_ring
end Owner1007.NorthForcedRing12
