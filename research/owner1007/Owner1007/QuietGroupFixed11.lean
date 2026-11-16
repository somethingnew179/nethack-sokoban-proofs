import Owner1007.PaidCount11
namespace Owner1007.QuietGroupFixed11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem weaken {paid narrower state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (imp : ∀c d,narrower c d→paid c d) :
 UpperQuiet11.Quiet narrower state group dirs final pushes moves outcomes := by
 induction quiet with
 |nil=>exact .nil _ _
 |cons head effect avoid tail ih=>
  refine .cons head effect ?_ ih
  rintro ⟨source,owner,metadata,pays⟩
  exact avoid ⟨source,owner,metadata,imp source _ pays⟩

theorem whole_fixed {paid state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (pays : ∀c,c∈group→∀d,paid c d) : ownPushes group outcomes=0 := by
 induction quiet with
 |nil=>rfl
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
  have headZero : ownPush group outcome=0 := by
   cases outcome with
   |walk c=>rfl
   |push source ending=>
    by_cases owner : source∈group
    ·exact False.elim (avoid ((PaidCount11.owned_iff effect).mp ⟨owner,pays source owner dir⟩))
    ·simp only [ownPush,if_neg owner]
  have same := ownPush_zero_update group outcome headZero
  have tailPays : ∀c,c∈update group outcome→∀d,paid c d := by rw [same];exact pays
  have zero := ih tailPays
  simpa only [ownPushes,headZero,Nat.zero_add] using zero
#print axioms weaken
#print axioms whole_fixed
end Owner1007.QuietGroupFixed11
