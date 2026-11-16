import Owner1007.LoggedCut
namespace Owner1007.OutcomeCuts
/-- Distinct chosen outcomes in the same trace have one of the two strict orders. -/
theorem compare {α : Type} {headA headB : α} (different : headA≠headB)
 (beforeA beforeB afterA afterB : List α)
 (same : beforeA++headA::afterA=beforeB++headB::afterB) :
 (∃ between,beforeB=beforeA++headA::between ∧afterA=between++headB::afterB) ∨
 (∃ between,beforeA=beforeB++headB::between ∧afterB=between++headA::afterA) := by
 induction beforeA generalizing beforeB with
 | nil =>
   cases beforeB with
   | nil =>
     have eq := (List.cons.inj same).1
     exact False.elim (different eq)
   | cons b rest =>
     have parts := List.cons.inj same
     have eq : headA=b := parts.1
     subst b
     exact Or.inl ⟨rest,rfl,parts.2⟩
 | cons a rest ih =>
   cases beforeB with
   | nil =>
     have parts := List.cons.inj same
     have eq : a=headB := parts.1
     subst a
     exact Or.inr ⟨rest,rfl,parts.2.symm⟩
   | cons b restB =>
     have parts := List.cons.inj same
     have eq : a=b := parts.1
     subst b
     rcases ih restB parts.2 with ⟨between,first,last⟩|⟨between,first,last⟩
     · exact Or.inl ⟨between,by simpa only [List.cons_append] using congrArg (List.cons a) first,last⟩
     · exact Or.inr ⟨between,by simpa only [List.cons_append] using congrArg (List.cons a) first,last⟩
#print axioms compare
end Owner1007.OutcomeCuts
