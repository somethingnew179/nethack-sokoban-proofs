import Owner1007.InwardMarkedStart11
import Owner1007.TaggedGatesFive11
import Owner1007.ForwardInwardImpossible11
namespace Owner1007.InwardMarkedEntry11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.InwardMarkedStart11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def incoming (i : Fin 8) : Cell:=ForwardInwardImpossible11.source (gate i)
def direction (i : Fin 8) : Dir:=ForwardInwardImpossible11.direction (gate i)
def a (i : Fin 8) : Cell:=if (gate i).val=0 then 138 else 137
def b (i : Fin 8) : Cell:=if (gate i).val=0 then 139 else 138
theorem at_phase {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (i : Fin 8) (head : step soko1_1.board state (direction i)=some t)
 (effect : Matches state t (.push (incoming i) (.stay 138)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++.push (incoming i) (.stay 138)::after)≤6)
 (leftCap : energy soko1_1.initial final [212] (before++.push (incoming i) (.stay 138)::after)≤2)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++.push (incoming i) (.stay 138)::after)<2)
 (prefixPair : 2≤energy soko1_1.initial state TightSplit11.A before)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (tag188 : endGroup [188] before=[u i]) (tag191 : endGroup [191] before=[189]) (tag212 : endGroup [212] before=[marker i]) : False:=by
 let one : Logged soko1_1.board state [direction i] t.state t.pushCost 1 [.push (incoming i) (.stay 138)]:=.cons head effect (.nil _)
 let extended:=first.append one
 have sequence : (before++[.push (incoming i) (.stay 138)])++after=before++.push (incoming i) (.stay 138)::after:=by simp only [List.append_assoc,List.singleton_append]
 have afterUpper : energy soko1_1.initial final UpperBudget11.U6 ((before++[.push (incoming i) (.stay 138)])++after)≤6:=by rw [sequence];exact upperCap
 have afterLeft : energy soko1_1.initial final [212] ((before++[.push (incoming i) (.stay 138)])++after)≤2:=by rw [sequence];exact leftCap
 have afterRest : energy soko1_1.initial final UpperBudget11.Rest ((before++[.push (incoming i) (.stay 138)])++after)<2:=by rw [sequence];exact restCap
 have next137 : endGroup [137] (before++[.push (incoming i) (.stay 138)])=[a i]:=by
  rw [endGroup_append,no_push_unchanged _ _ zero137]
  have all : ∀i,endGroup [137] [.push (incoming i) (.stay 138)]=[a i]:=by decide +kernel
  exact all i
 have next139 : endGroup [139] (before++[.push (incoming i) (.stay 138)])=[b i]:=by
  rw [endGroup_append,no_push_unchanged _ _ zero139]
  have all : ∀i,endGroup [139] [.push (incoming i) (.stay 138)]=[b i]:=by decide +kernel
  exact all i
 have next188 : endGroup [188] (before++[.push (incoming i) (.stay 138)])=[u i]:=by
  rw [endGroup_append,tag188]
  have all : ∀i,endGroup [u i] [.push (incoming i) (.stay 138)]=[u i]:=by decide +kernel
  exact all i
 have next191 : endGroup [191] (before++[.push (incoming i) (.stay 138)])=[189]:=by
  rw [endGroup_append,tag191]
  have all : ∀i,endGroup [189] [.push (incoming i) (.stay 138)]=[189]:=by decide +kernel
  exact all i
 have next212 : endGroup [212] (before++[.push (incoming i) (.stay 138)])=[marker i]:=by
  rw [endGroup_append,tag212]
  have all : ∀i,endGroup [marker i] [.push (incoming i) (.stay 138)]=[marker i]:=by decide +kernel
  exact all i
 have facts:=TaggedGatesFive11.owned extended last completed afterUpper afterLeft
  (a i) (b i) (u i) 189 (marker i) next137 next139 next188 next191 next212
 have same : ([a i,b i,u i,189,marker i]:List Cell).Perm (locks i):=by
  have all : ∀i,([a i,b i,u i,189,marker i]:List Cell).Perm (locks i):=by decide +kernel
  exact all i
 have physical : locks i⊆t.state.boulders:=fun c h=>facts.2.1 (same.mem_iff.mpr h)
 have equalEnd:=endGroup_perm same after
 rw [facts.2.2] at equalEnd
 have gone : endGroup (locks i) after=[]:=List.perm_nil.mp equalEnd.symm
 have oldOther : ownPushes [other i] before=0:=by
  have options : ∀i,other i=137∨other i=139:=by decide +kernel
  rcases options i with h|h
  ·simpa only [h] using zero137
  ·simpa only [h] using zero139
 have nextOther : ownPushes [other i] (before++[.push (incoming i) (.stay 138)])=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ oldOther,oldOther]
  have all : ∀i,ownPushes [other i] [.push (incoming i) (.stay 138)]=0:=by decide +kernel
  simpa only [Nat.zero_add] using all i
 have monotone:=prefix_energy_le first one TightSplit11.A (by decide) (by decide)
 have nextPair : 2≤energy soko1_1.initial t.state TightSplit11.A (before++[.push (incoming i) (.stay 138)]):=by omega
 have hero : t.state.player∈region i:=by
  rw [effect.2]
  have all : ∀i,incoming i∈region i:=by decide +kernel
  exact all i
 exact InwardMarkedStart11.impossible extended last completed afterUpper afterRest nextPair i nextOther next188 next191 physical hero gone
theorem phase_exists (kind : Fin 2) (parked mark : Cell)
 (parkedCases : parked=186∨parked=187) (markCases : mark=213∨mark=214) :
 ∃i : Fin 8,gate i=kind∧u i=parked∧marker i=mark:=by
 obtain ⟨kind,bound⟩:=kind
 have kindCases : kind=0∨kind=1:=by omega
 have uBound : (if parked=186 then 2 else 0)≤2:=by split <;> omega
 have mBound : (if mark=214 then 4 else 0)≤4:=by split <;> omega
 let i : Fin 8:=⟨kind+(if parked=186 then 2 else 0)+(if mark=214 then 4 else 0),by omega⟩
 refine ⟨i,?_,?_,?_⟩
 all_goals
  rcases parkedCases with rfl|rfl <;> rcases markCases with rfl|rfl <;> rcases kindCases with rfl|rfl <;> simp [i,gate,u,marker]

theorem after_inward_impossible {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (kind : Fin 2) (parked mark : Cell) (parkedCases : parked=186∨parked=187) (markCases : mark=213∨mark=214)
 (head : step soko1_1.board state (ForwardInwardImpossible11.direction kind)=some t)
 (effect : Matches state t (.push (ForwardInwardImpossible11.source kind) (.stay 138)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++.push (ForwardInwardImpossible11.source kind) (.stay 138)::after)≤6)
 (leftCap : energy soko1_1.initial final [212] (before++.push (ForwardInwardImpossible11.source kind) (.stay 138)::after)≤2)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++.push (ForwardInwardImpossible11.source kind) (.stay 138)::after)<2)
 (prefixPair : 2≤energy soko1_1.initial state TightSplit11.A before)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (tag188 : endGroup [188] before=[parked]) (tag191 : endGroup [191] before=[189]) (tag212 : endGroup [212] before=[mark]) : False:=by
 obtain ⟨i,gateEq,uEq,markerEq⟩:=phase_exists kind parked mark parkedCases markCases
 exact at_phase first i
  (by simpa only [direction,gateEq] using head)
  (by simpa only [incoming,gateEq] using effect)
  last completed (by simpa only [incoming,gateEq] using upperCap)
  (by simpa only [incoming,gateEq] using leftCap) (by simpa only [incoming,gateEq] using restCap)
  prefixPair zero137 zero139 (by rw [uEq];exact tag188) tag191 (by rw [markerEq];exact tag212)
#print axioms at_phase
#print axioms phase_exists
#print axioms after_inward_impossible
end Owner1007.InwardMarkedEntry11
