import Owner1007.WestRankHead11
namespace Owner1007.Side265Clear11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern

theorem both {state : State} {dir : Dir} {t : Transition}
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some 265)
 (side : dir=.east∨dir=.west) : 264∉state.boulders ∧266∉state.boulders := by
 rcases step_cases_full _ _ _ _ checked with walked|pushed
 ·obtain ⟨target,_,_,_,_,shape⟩ := walked
  simp only [shape] at metadata
  contradiction
 ·obtain ⟨source,result,adjacent,_,_,push,shape⟩ := pushed
  have same : source=265 := by simpa only [shape,Option.some.injEq] using metadata
  subst source
  have clear := step_player_clear _ _ _ _ checked
  have behind := Geometry.reverseCheck_sound soko1_1.board Owner1007.ZeroWord11.reverse_checked state.player clear.1 dir 265 adjacent
  obtain ⟨dest,next,_,_,free⟩ := (push_first_clear _ _ _ _ _ push).2
  rcases side with rfl|rfl
  ·have playerEq : state.player=264 := Option.some.inj (behind.symm.trans (show advance soko1_1.board 265 Dir.east.opposite=some 264 by decide +kernel))
   have destEq : dest=266 := Option.some.inj (next.symm.trans (show advance soko1_1.board 265 .east=some 266 by decide +kernel))
   exact ⟨playerEq ▸ clear.2.2.1,destEq ▸ free⟩
  ·have playerEq : state.player=266 := Option.some.inj (behind.symm.trans (show advance soko1_1.board 265 Dir.west.opposite=some 266 by decide +kernel))
   have destEq : dest=264 := Option.some.inj (next.symm.trans (show advance soko1_1.board 265 .west=some 264 by decide +kernel))
   exact ⟨destEq ▸ free,playerEq ▸ clear.2.2.1⟩
#print axioms both
end Owner1007.Side265Clear11
