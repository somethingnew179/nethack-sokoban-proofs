import Owner1007.RightParkedSix11
import Owner1007.RightParkedRestNext11
import Owner1007.RightParkedRestFront11
import Owner1007.InwardMarkedEntry11
namespace Owner1007.RightParkedRestInduction11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.RightParkedSix11 Owner1007.RightParkedRestReady11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def rank (i : Fin 4) : Nat:=match i.val with |0=>1|1=>0|2=>2|_=>1
theorem next_lower (i j : Fin 4) (source target : Cell) (next : Next i j source target) : rank j<rank i:=by
 rcases next with ⟨a,b,_,_⟩|⟨a,b,_,_⟩|⟨a,b,_,_⟩
 ·have ai:i=0:=Fin.ext a
  have bj:j=1:=Fin.ext b
  subst i;subst j;decide
 ·have ai:i=2:=Fin.ext a
  have bj:j=0:=Fin.ext b
  subst i;subst j;decide
 ·have ai:i=3:=Fin.ext a
  have bj:j=1:=Fin.ext b
  subst i;subst j;decide

theorem head_false {beforeDirs state beforePushes beforeMoves before dir t outcome dirs final pushes moves outcomes i source}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i)
 (metadata : t.pushSource=some source) (shape : Shape i source dir)
 (laterCases : ∀j,rank j<rank i→Ready (first.append (Logged.cons head effect (Logged.nil _))) last j→False) : False:=by
 have ordinary (s target : Cell) (d : Dir) (same : dir=d) (headMeta : t.pushSource=some s)
    (targets : pushTargets soko1_1.board s d=[target]) (noHole : target∉soko1_1.initial.holes) :
    outcome=.push s (.stay target):=by
  have checked : step soko1_1.board state d=some t:=by simpa only [same] using head
  exact UpperHeadCases11.ordinary_effect checked effect headMeta targets noHole first.trace.holes_sublist.subset
 have parkedCases : u i=186∨u i=187:=by unfold u;split<;>simp
 have markCases : marker i=213∨marker i=214:=by unfold marker;split<;>simp
 rcases shape with ⟨gateCases,directionCases⟩|⟨at0,rfl,rfl⟩|⟨at1,rfl,rfl⟩|⟨small,rfl,rfl⟩|⟨rfl,rfl⟩|⟨small,rfl,rfl⟩|⟨at1,rfl,rfl⟩|⟨large,rfl,rfl⟩
 ·rcases gateCases with rfl|rfl
  ·rcases directionCases with rfl|rfl
   ·have headEq:=ordinary 137 138 .east rfl metadata (by decide +kernel) (by decide +kernel)
    subst outcome
    exact InwardMarkedEntry11.after_inward_impossible first 0 (u i) (marker i) parkedCases markCases head effect last
     ready.completed ready.upper ready.left212 ready.rest ready.pairTwo ready.zero137 ready.zero139 ready.tag188 ready.tag191 ready.tag212
   ·have headEq:=ordinary 137 136 .west rfl metadata (by decide +kernel) (by decide +kernel)
    subst outcome
    exact outward137_absurd first head effect last ready
  ·rcases directionCases with rfl|rfl
   ·have headEq:=ordinary 139 140 .east rfl metadata (by decide +kernel) (by decide +kernel)
    subst outcome
    exact outward139_absurd first head effect last ready
   ·have headEq:=ordinary 139 138 .west rfl metadata (by decide +kernel) (by decide +kernel)
    subst outcome
    exact InwardMarkedEntry11.after_inward_impossible first 1 (u i) (marker i) parkedCases markCases head effect last
     ready.completed ready.upper ready.left212 ready.rest ready.pairTwo ready.zero137 ready.zero139 ready.tag188 ready.tag191 ready.tag212
 ·have headEq:=ordinary 187 186 .west rfl metadata (by decide +kernel) (by decide +kernel)
  have next : Next i 1 187 186:=Or.inl ⟨at0,rfl,rfl,rfl⟩
  have future:=after_ready first head effect last ready rfl headEq next
  exact laterCases 1 (next_lower i 1 187 186 next) future
 ·have headEq:=ordinary 186 185 .west rfl metadata (by decide +kernel) (by decide +kernel)
  subst outcome
  have atI:i=1:=Fin.ext at1
  have up186 : u i=186:=by subst i;rfl
  exact u_west_absurd first head effect last ready up186
 ·have headEq:=ordinary 189 190 .east rfl metadata (by decide +kernel) (by decide +kernel)
  subst outcome
  exact q_east_absurd first head effect last ready
 ·have headEq:=ordinary 189 188 .west rfl metadata (by decide +kernel) (by decide +kernel)
  subst outcome
  exact q_west_absurd first head effect last ready
 ·have headEq:=ordinary 213 212 .west rfl metadata (by decide +kernel) (by decide +kernel)
  subst outcome
  have markerEq : marker i=213:=by unfold marker;simp [small]
  exact front_west_absurd first head effect last ready markerEq
 ·have headEq:=ordinary 213 239 .south rfl metadata (by decide +kernel) (by decide +kernel)
  subst outcome
  have atI:i=1:=Fin.ext at1
  have markerEq : marker i=213:=by subst i;rfl
  exact front_south_absurd first head effect last ready markerEq
 ·have headEq:=ordinary 214 213 .west rfl metadata (by decide +kernel) (by decide +kernel)
  have cases:i.val=2∨i.val=3:=by have bound:=i.isLt;omega
  rcases cases with at2|at3
  ·have next : Next i 0 214 213:=Or.inr (Or.inl ⟨at2,rfl,rfl,rfl⟩)
   have future:=after_ready first head effect last ready rfl headEq next
   exact laterCases 0 (next_lower i 0 214 213 next) future
  ·have next : Next i 1 214 213:=Or.inr (Or.inr ⟨at3,rfl,rfl,rfl⟩)
   have future:=after_ready first head effect last ready rfl headEq next
   exact laterCases 1 (next_lower i 1 214 213 next) future

def Impossible (i : Fin 4) : Prop:=∀{beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes},
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)→
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)→Ready first logged i→False

theorem step (i : Fin 4) (laterCases : ∀j,rank j<rank i→Impossible j) : Impossible i:=by
 intro beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes first logged ready
 obtain ⟨cut,zero,heroBefore,source,member,metadata,shape⟩:=RightParkedSix11.first_exit first.trace logged i ready.physical ready.hero ready.gone
 have beforeReady:=before_ready first logged ready cut heroBefore
 exact head_false (first.append cut.before.logged) cut.headChecked cut.headEffect cut.after beforeReady metadata shape
  (fun j less future=>laterCases j less _ _ future)

theorem impossible {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 4) (ready : Ready first logged i) : False:=by
 have one : Impossible 1:=by
  apply step 1
  intro j less
  have none : ∀j:Fin 4,¬rank j<rank 1:=by decide
  exact (False.elim (none j less) : Impossible j)
 have zero : Impossible 0:=by
  apply step 0
  intro j less
  have single : ∀j:Fin 4,rank j<rank 0→j=1:=by decide
  have same:=single j less
  subst j;exact @one
 have three : Impossible 3:=by
  apply step 3
  intro j less
  have single : ∀j:Fin 4,rank j<rank 3→j=1:=by decide
  have same:=single j less
  subst j;exact @one
 have two : Impossible 2:=by
  apply step 2
  intro j less
  have options : ∀j:Fin 4,rank j<rank 2→j=0∨j=1∨j=3:=by decide
  rcases options j less with rfl|rfl|rfl
  ·exact @zero
  ·exact @one
  ·exact @three
 have options : i=0∨i=1∨i=2∨i=3:=by have bound:=i.isLt;omega
 rcases options with rfl|rfl|rfl|rfl
 ·exact zero first logged ready
 ·exact one first logged ready
 ·exact two first logged ready
 ·exact three first logged ready
#print axioms head_false
#print axioms impossible
end Owner1007.RightParkedRestInduction11
