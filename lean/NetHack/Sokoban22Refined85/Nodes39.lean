/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes38
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4680 (p : Pattern) : Int := if p 141 then d4679 p else d4676 p
theorem agree4680 (p q : Pattern) (h : Agree support p q) : d4680 p = d4680 q := by
  simp only [d4680, h 141 (by decide), agree4679 p q h, agree4676 p q h]
theorem nonnegative4680 (p : Pattern) : 0 ≤ d4680 p :=
  nonnegative_ite (p 141) (nonnegative4679 p) (nonnegative4676 p)
def d4681 (p : Pattern) : Int := if p 161 then d53 p else d16 p
theorem agree4681 (p q : Pattern) (h : Agree support p q) : d4681 p = d4681 q := by
  simp only [d4681, h 161 (by decide), agree53 p q h, agree16 p q h]
theorem nonnegative4681 (p : Pattern) : 0 ≤ d4681 p :=
  nonnegative_ite (p 161) (nonnegative53 p) (nonnegative16 p)
def d4682 (p : Pattern) : Int := if p 161 then d12 p else d53 p
theorem agree4682 (p q : Pattern) (h : Agree support p q) : d4682 p = d4682 q := by
  simp only [d4682, h 161 (by decide), agree12 p q h, agree53 p q h]
theorem nonnegative4682 (p : Pattern) : 0 ≤ d4682 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative53 p)
def d4683 (p : Pattern) : Int := if p 160 then d4682 p else d4681 p
theorem agree4683 (p q : Pattern) (h : Agree support p q) : d4683 p = d4683 q := by
  simp only [d4683, h 160 (by decide), agree4682 p q h, agree4681 p q h]
theorem nonnegative4683 (p : Pattern) : 0 ≤ d4683 p :=
  nonnegative_ite (p 160) (nonnegative4682 p) (nonnegative4681 p)
def d4684 (p : Pattern) : Int := if p 161 then d20 p else d53 p
theorem agree4684 (p q : Pattern) (h : Agree support p q) : d4684 p = d4684 q := by
  simp only [d4684, h 161 (by decide), agree20 p q h, agree53 p q h]
theorem nonnegative4684 (p : Pattern) : 0 ≤ d4684 p :=
  nonnegative_ite (p 161) (nonnegative20 p) (nonnegative53 p)
def d4685 (p : Pattern) : Int := if p 161 then d12 p else d20 p
theorem agree4685 (p q : Pattern) (h : Agree support p q) : d4685 p = d4685 q := by
  simp only [d4685, h 161 (by decide), agree12 p q h, agree20 p q h]
theorem nonnegative4685 (p : Pattern) : 0 ≤ d4685 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative20 p)
def d4686 (p : Pattern) : Int := if p 160 then d4685 p else d4684 p
theorem agree4686 (p q : Pattern) (h : Agree support p q) : d4686 p = d4686 q := by
  simp only [d4686, h 160 (by decide), agree4685 p q h, agree4684 p q h]
theorem nonnegative4686 (p : Pattern) : 0 ≤ d4686 p :=
  nonnegative_ite (p 160) (nonnegative4685 p) (nonnegative4684 p)
def d4687 (p : Pattern) : Int := if p 141 then d4686 p else d4683 p
theorem agree4687 (p q : Pattern) (h : Agree support p q) : d4687 p = d4687 q := by
  simp only [d4687, h 141 (by decide), agree4686 p q h, agree4683 p q h]
theorem nonnegative4687 (p : Pattern) : 0 ≤ d4687 p :=
  nonnegative_ite (p 141) (nonnegative4686 p) (nonnegative4683 p)
def d4688 (p : Pattern) : Int := if p 138 then d4687 p else d4680 p
theorem agree4688 (p q : Pattern) (h : Agree support p q) : d4688 p = d4688 q := by
  simp only [d4688, h 138 (by decide), agree4687 p q h, agree4680 p q h]
theorem nonnegative4688 (p : Pattern) : 0 ≤ d4688 p :=
  nonnegative_ite (p 138) (nonnegative4687 p) (nonnegative4680 p)
def d4689 (p : Pattern) : Int := if p 161 then d12 p else d62 p
theorem agree4689 (p q : Pattern) (h : Agree support p q) : d4689 p = d4689 q := by
  simp only [d4689, h 161 (by decide), agree12 p q h, agree62 p q h]
theorem nonnegative4689 (p : Pattern) : 0 ≤ d4689 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative62 p)
def d4690 (p : Pattern) : Int := if p 160 then d12 p else d4689 p
theorem agree4690 (p q : Pattern) (h : Agree support p q) : d4690 p = d4690 q := by
  simp only [d4690, h 160 (by decide), agree12 p q h, agree4689 p q h]
theorem nonnegative4690 (p : Pattern) : 0 ≤ d4690 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4689 p)
def d4691 (p : Pattern) : Int := if p 141 then d12 p else d4690 p
theorem agree4691 (p q : Pattern) (h : Agree support p q) : d4691 p = d4691 q := by
  simp only [d4691, h 141 (by decide), agree12 p q h, agree4690 p q h]
theorem nonnegative4691 (p : Pattern) : 0 ≤ d4691 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative4690 p)
def d4692 (p : Pattern) : Int := if p 138 then d4691 p else d4687 p
theorem agree4692 (p q : Pattern) (h : Agree support p q) : d4692 p = d4692 q := by
  simp only [d4692, h 138 (by decide), agree4691 p q h, agree4687 p q h]
theorem nonnegative4692 (p : Pattern) : 0 ≤ d4692 p :=
  nonnegative_ite (p 138) (nonnegative4691 p) (nonnegative4687 p)
def d4693 (p : Pattern) : Int := if p 116 then d4692 p else d4688 p
theorem agree4693 (p q : Pattern) (h : Agree support p q) : d4693 p = d4693 q := by
  simp only [d4693, h 116 (by decide), agree4692 p q h, agree4688 p q h]
theorem nonnegative4693 (p : Pattern) : 0 ≤ d4693 p :=
  nonnegative_ite (p 116) (nonnegative4692 p) (nonnegative4688 p)
def d4694 (p : Pattern) : Int := if p 138 then d12 p else d4687 p
theorem agree4694 (p q : Pattern) (h : Agree support p q) : d4694 p = d4694 q := by
  simp only [d4694, h 138 (by decide), agree12 p q h, agree4687 p q h]
theorem nonnegative4694 (p : Pattern) : 0 ≤ d4694 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4687 p)
def d4695 (p : Pattern) : Int := if p 116 then d4694 p else d4688 p
theorem agree4695 (p q : Pattern) (h : Agree support p q) : d4695 p = d4695 q := by
  simp only [d4695, h 116 (by decide), agree4694 p q h, agree4688 p q h]
theorem nonnegative4695 (p : Pattern) : 0 ≤ d4695 p :=
  nonnegative_ite (p 116) (nonnegative4694 p) (nonnegative4688 p)
def d4696 (p : Pattern) : Int := if p 115 then d4695 p else d4693 p
theorem agree4696 (p q : Pattern) (h : Agree support p q) : d4696 p = d4696 q := by
  simp only [d4696, h 115 (by decide), agree4695 p q h, agree4693 p q h]
theorem nonnegative4696 (p : Pattern) : 0 ≤ d4696 p :=
  nonnegative_ite (p 115) (nonnegative4695 p) (nonnegative4693 p)
def d4697 (p : Pattern) : Int := if p 161 then d118 p else d105 p
theorem agree4697 (p q : Pattern) (h : Agree support p q) : d4697 p = d4697 q := by
  simp only [d4697, h 161 (by decide), agree118 p q h, agree105 p q h]
theorem nonnegative4697 (p : Pattern) : 0 ≤ d4697 p :=
  nonnegative_ite (p 161) (nonnegative118 p) (nonnegative105 p)
def d4698 (p : Pattern) : Int := if p 161 then d125 p else d118 p
theorem agree4698 (p q : Pattern) (h : Agree support p q) : d4698 p = d4698 q := by
  simp only [d4698, h 161 (by decide), agree125 p q h, agree118 p q h]
theorem nonnegative4698 (p : Pattern) : 0 ≤ d4698 p :=
  nonnegative_ite (p 161) (nonnegative125 p) (nonnegative118 p)
def d4699 (p : Pattern) : Int := if p 160 then d4698 p else d4697 p
theorem agree4699 (p q : Pattern) (h : Agree support p q) : d4699 p = d4699 q := by
  simp only [d4699, h 160 (by decide), agree4698 p q h, agree4697 p q h]
theorem nonnegative4699 (p : Pattern) : 0 ≤ d4699 p :=
  nonnegative_ite (p 160) (nonnegative4698 p) (nonnegative4697 p)
def d4700 (p : Pattern) : Int := if p 161 then d861 p else d132 p
theorem agree4700 (p q : Pattern) (h : Agree support p q) : d4700 p = d4700 q := by
  simp only [d4700, h 161 (by decide), agree861 p q h, agree132 p q h]
theorem nonnegative4700 (p : Pattern) : 0 ≤ d4700 p :=
  nonnegative_ite (p 161) (nonnegative861 p) (nonnegative132 p)
def d4701 (p : Pattern) : Int := if p 161 then d229 p else d861 p
theorem agree4701 (p q : Pattern) (h : Agree support p q) : d4701 p = d4701 q := by
  simp only [d4701, h 161 (by decide), agree229 p q h, agree861 p q h]
theorem nonnegative4701 (p : Pattern) : 0 ≤ d4701 p :=
  nonnegative_ite (p 161) (nonnegative229 p) (nonnegative861 p)
def d4702 (p : Pattern) : Int := if p 160 then d4701 p else d4700 p
theorem agree4702 (p q : Pattern) (h : Agree support p q) : d4702 p = d4702 q := by
  simp only [d4702, h 160 (by decide), agree4701 p q h, agree4700 p q h]
theorem nonnegative4702 (p : Pattern) : 0 ≤ d4702 p :=
  nonnegative_ite (p 160) (nonnegative4701 p) (nonnegative4700 p)
def d4703 (p : Pattern) : Int := if p 141 then d4702 p else d4699 p
theorem agree4703 (p q : Pattern) (h : Agree support p q) : d4703 p = d4703 q := by
  simp only [d4703, h 141 (by decide), agree4702 p q h, agree4699 p q h]
theorem nonnegative4703 (p : Pattern) : 0 ≤ d4703 p :=
  nonnegative_ite (p 141) (nonnegative4702 p) (nonnegative4699 p)
def d4704 (p : Pattern) : Int := if p 161 then d132 p else d105 p
theorem agree4704 (p q : Pattern) (h : Agree support p q) : d4704 p = d4704 q := by
  simp only [d4704, h 161 (by decide), agree132 p q h, agree105 p q h]
theorem nonnegative4704 (p : Pattern) : 0 ≤ d4704 p :=
  nonnegative_ite (p 161) (nonnegative132 p) (nonnegative105 p)
def d4705 (p : Pattern) : Int := if p 161 then d12 p else d132 p
theorem agree4705 (p q : Pattern) (h : Agree support p q) : d4705 p = d4705 q := by
  simp only [d4705, h 161 (by decide), agree12 p q h, agree132 p q h]
theorem nonnegative4705 (p : Pattern) : 0 ≤ d4705 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative132 p)
def d4706 (p : Pattern) : Int := if p 160 then d4705 p else d4704 p
theorem agree4706 (p q : Pattern) (h : Agree support p q) : d4706 p = d4706 q := by
  simp only [d4706, h 160 (by decide), agree4705 p q h, agree4704 p q h]
theorem nonnegative4706 (p : Pattern) : 0 ≤ d4706 p :=
  nonnegative_ite (p 160) (nonnegative4705 p) (nonnegative4704 p)
def d4707 (p : Pattern) : Int := if p 161 then d109 p else d132 p
theorem agree4707 (p q : Pattern) (h : Agree support p q) : d4707 p = d4707 q := by
  simp only [d4707, h 161 (by decide), agree109 p q h, agree132 p q h]
theorem nonnegative4707 (p : Pattern) : 0 ≤ d4707 p :=
  nonnegative_ite (p 161) (nonnegative109 p) (nonnegative132 p)
def d4708 (p : Pattern) : Int := if p 161 then d12 p else d109 p
theorem agree4708 (p q : Pattern) (h : Agree support p q) : d4708 p = d4708 q := by
  simp only [d4708, h 161 (by decide), agree12 p q h, agree109 p q h]
theorem nonnegative4708 (p : Pattern) : 0 ≤ d4708 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative109 p)
def d4709 (p : Pattern) : Int := if p 160 then d4708 p else d4707 p
theorem agree4709 (p q : Pattern) (h : Agree support p q) : d4709 p = d4709 q := by
  simp only [d4709, h 160 (by decide), agree4708 p q h, agree4707 p q h]
theorem nonnegative4709 (p : Pattern) : 0 ≤ d4709 p :=
  nonnegative_ite (p 160) (nonnegative4708 p) (nonnegative4707 p)
def d4710 (p : Pattern) : Int := if p 141 then d4709 p else d4706 p
theorem agree4710 (p q : Pattern) (h : Agree support p q) : d4710 p = d4710 q := by
  simp only [d4710, h 141 (by decide), agree4709 p q h, agree4706 p q h]
theorem nonnegative4710 (p : Pattern) : 0 ≤ d4710 p :=
  nonnegative_ite (p 141) (nonnegative4709 p) (nonnegative4706 p)
def d4711 (p : Pattern) : Int := if p 138 then d4710 p else d4703 p
theorem agree4711 (p q : Pattern) (h : Agree support p q) : d4711 p = d4711 q := by
  simp only [d4711, h 138 (by decide), agree4710 p q h, agree4703 p q h]
theorem nonnegative4711 (p : Pattern) : 0 ≤ d4711 p :=
  nonnegative_ite (p 138) (nonnegative4710 p) (nonnegative4703 p)
def d4712 (p : Pattern) : Int := if p 138 then d12 p else d4710 p
theorem agree4712 (p q : Pattern) (h : Agree support p q) : d4712 p = d4712 q := by
  simp only [d4712, h 138 (by decide), agree12 p q h, agree4710 p q h]
theorem nonnegative4712 (p : Pattern) : 0 ≤ d4712 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4710 p)
def d4713 (p : Pattern) : Int := if p 116 then d4712 p else d4711 p
theorem agree4713 (p q : Pattern) (h : Agree support p q) : d4713 p = d4713 q := by
  simp only [d4713, h 116 (by decide), agree4712 p q h, agree4711 p q h]
theorem nonnegative4713 (p : Pattern) : 0 ≤ d4713 p :=
  nonnegative_ite (p 116) (nonnegative4712 p) (nonnegative4711 p)
def d4714 (p : Pattern) : Int := if p 71 then d4713 p else d4696 p
theorem agree4714 (p q : Pattern) (h : Agree support p q) : d4714 p = d4714 q := by
  simp only [d4714, h 71 (by decide), agree4713 p q h, agree4696 p q h]
theorem nonnegative4714 (p : Pattern) : 0 ≤ d4714 p :=
  nonnegative_ite (p 71) (nonnegative4713 p) (nonnegative4696 p)
def d4715 (p : Pattern) : Int := if p 49 then d4714 p else d4696 p
theorem agree4715 (p q : Pattern) (h : Agree support p q) : d4715 p = d4715 q := by
  simp only [d4715, h 49 (by decide), agree4714 p q h, agree4696 p q h]
theorem nonnegative4715 (p : Pattern) : 0 ≤ d4715 p :=
  nonnegative_ite (p 49) (nonnegative4714 p) (nonnegative4696 p)
def d4716 (p : Pattern) : Int := if p 161 then d269 p else d105 p
theorem agree4716 (p q : Pattern) (h : Agree support p q) : d4716 p = d4716 q := by
  simp only [d4716, h 161 (by decide), agree269 p q h, agree105 p q h]
theorem nonnegative4716 (p : Pattern) : 0 ≤ d4716 p :=
  nonnegative_ite (p 161) (nonnegative269 p) (nonnegative105 p)
def d4717 (p : Pattern) : Int := if p 161 then d274 p else d269 p
theorem agree4717 (p q : Pattern) (h : Agree support p q) : d4717 p = d4717 q := by
  simp only [d4717, h 161 (by decide), agree274 p q h, agree269 p q h]
theorem nonnegative4717 (p : Pattern) : 0 ≤ d4717 p :=
  nonnegative_ite (p 161) (nonnegative274 p) (nonnegative269 p)
def d4718 (p : Pattern) : Int := if p 160 then d4717 p else d4716 p
theorem agree4718 (p q : Pattern) (h : Agree support p q) : d4718 p = d4718 q := by
  simp only [d4718, h 160 (by decide), agree4717 p q h, agree4716 p q h]
theorem nonnegative4718 (p : Pattern) : 0 ≤ d4718 p :=
  nonnegative_ite (p 160) (nonnegative4717 p) (nonnegative4716 p)
def d4719 (p : Pattern) : Int := if p 161 then d298 p else d132 p
theorem agree4719 (p q : Pattern) (h : Agree support p q) : d4719 p = d4719 q := by
  simp only [d4719, h 161 (by decide), agree298 p q h, agree132 p q h]
theorem nonnegative4719 (p : Pattern) : 0 ≤ d4719 p :=
  nonnegative_ite (p 161) (nonnegative298 p) (nonnegative132 p)
def d4720 (p : Pattern) : Int := if p 161 then d1127 p else d298 p
theorem agree4720 (p q : Pattern) (h : Agree support p q) : d4720 p = d4720 q := by
  simp only [d4720, h 161 (by decide), agree1127 p q h, agree298 p q h]
theorem nonnegative4720 (p : Pattern) : 0 ≤ d4720 p :=
  nonnegative_ite (p 161) (nonnegative1127 p) (nonnegative298 p)
def d4721 (p : Pattern) : Int := if p 160 then d4720 p else d4719 p
theorem agree4721 (p q : Pattern) (h : Agree support p q) : d4721 p = d4721 q := by
  simp only [d4721, h 160 (by decide), agree4720 p q h, agree4719 p q h]
theorem nonnegative4721 (p : Pattern) : 0 ≤ d4721 p :=
  nonnegative_ite (p 160) (nonnegative4720 p) (nonnegative4719 p)
def d4722 (p : Pattern) : Int := if p 141 then d4721 p else d4718 p
theorem agree4722 (p q : Pattern) (h : Agree support p q) : d4722 p = d4722 q := by
  simp only [d4722, h 141 (by decide), agree4721 p q h, agree4718 p q h]
theorem nonnegative4722 (p : Pattern) : 0 ≤ d4722 p :=
  nonnegative_ite (p 141) (nonnegative4721 p) (nonnegative4718 p)
def d4723 (p : Pattern) : Int := if p 138 then d4710 p else d4722 p
theorem agree4723 (p q : Pattern) (h : Agree support p q) : d4723 p = d4723 q := by
  simp only [d4723, h 138 (by decide), agree4710 p q h, agree4722 p q h]
theorem nonnegative4723 (p : Pattern) : 0 ≤ d4723 p :=
  nonnegative_ite (p 138) (nonnegative4710 p) (nonnegative4722 p)
def d4724 (p : Pattern) : Int := if p 116 then d4712 p else d4723 p
theorem agree4724 (p q : Pattern) (h : Agree support p q) : d4724 p = d4724 q := by
  simp only [d4724, h 116 (by decide), agree4712 p q h, agree4723 p q h]
theorem nonnegative4724 (p : Pattern) : 0 ≤ d4724 p :=
  nonnegative_ite (p 116) (nonnegative4712 p) (nonnegative4723 p)
def d4725 (p : Pattern) : Int := if p 115 then d4724 p else d4713 p
theorem agree4725 (p q : Pattern) (h : Agree support p q) : d4725 p = d4725 q := by
  simp only [d4725, h 115 (by decide), agree4724 p q h, agree4713 p q h]
theorem nonnegative4725 (p : Pattern) : 0 ≤ d4725 p :=
  nonnegative_ite (p 115) (nonnegative4724 p) (nonnegative4713 p)
def d4726 (p : Pattern) : Int := if p 71 then d4725 p else d4696 p
theorem agree4726 (p q : Pattern) (h : Agree support p q) : d4726 p = d4726 q := by
  simp only [d4726, h 71 (by decide), agree4725 p q h, agree4696 p q h]
theorem nonnegative4726 (p : Pattern) : 0 ≤ d4726 p :=
  nonnegative_ite (p 71) (nonnegative4725 p) (nonnegative4696 p)
def d4727 (p : Pattern) : Int := if p 49 then d4726 p else d4696 p
theorem agree4727 (p q : Pattern) (h : Agree support p q) : d4727 p = d4727 q := by
  simp only [d4727, h 49 (by decide), agree4726 p q h, agree4696 p q h]
theorem nonnegative4727 (p : Pattern) : 0 ≤ d4727 p :=
  nonnegative_ite (p 49) (nonnegative4726 p) (nonnegative4696 p)
def d4728 (p : Pattern) : Int := if p 48 then d4727 p else d4715 p
theorem agree4728 (p q : Pattern) (h : Agree support p q) : d4728 p = d4728 q := by
  simp only [d4728, h 48 (by decide), agree4727 p q h, agree4715 p q h]
theorem nonnegative4728 (p : Pattern) : 0 ≤ d4728 p :=
  nonnegative_ite (p 48) (nonnegative4727 p) (nonnegative4715 p)
def d4729 (p : Pattern) : Int := if p 141 then d65 p else d29 p
theorem agree4729 (p q : Pattern) (h : Agree support p q) : d4729 p = d4729 q := by
  simp only [d4729, h 141 (by decide), agree65 p q h, agree29 p q h]
theorem nonnegative4729 (p : Pattern) : 0 ≤ d4729 p :=
  nonnegative_ite (p 141) (nonnegative65 p) (nonnegative29 p)
def d4730 (p : Pattern) : Int := if p 141 then d93 p else d92 p
theorem agree4730 (p q : Pattern) (h : Agree support p q) : d4730 p = d4730 q := by
  simp only [d4730, h 141 (by decide), agree93 p q h, agree92 p q h]
theorem nonnegative4730 (p : Pattern) : 0 ≤ d4730 p :=
  nonnegative_ite (p 141) (nonnegative93 p) (nonnegative92 p)
def d4731 (p : Pattern) : Int := if p 138 then d4730 p else d4729 p
theorem agree4731 (p q : Pattern) (h : Agree support p q) : d4731 p = d4731 q := by
  simp only [d4731, h 138 (by decide), agree4730 p q h, agree4729 p q h]
theorem nonnegative4731 (p : Pattern) : 0 ≤ d4731 p :=
  nonnegative_ite (p 138) (nonnegative4730 p) (nonnegative4729 p)
def d4732 (p : Pattern) : Int := if p 116 then d4731 p else d4729 p
theorem agree4732 (p q : Pattern) (h : Agree support p q) : d4732 p = d4732 q := by
  simp only [d4732, h 116 (by decide), agree4731 p q h, agree4729 p q h]
theorem nonnegative4732 (p : Pattern) : 0 ≤ d4732 p :=
  nonnegative_ite (p 116) (nonnegative4731 p) (nonnegative4729 p)
def d4733 (p : Pattern) : Int := if p 138 then d12 p else d4729 p
theorem agree4733 (p q : Pattern) (h : Agree support p q) : d4733 p = d4733 q := by
  simp only [d4733, h 138 (by decide), agree12 p q h, agree4729 p q h]
theorem nonnegative4733 (p : Pattern) : 0 ≤ d4733 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4729 p)
def d4734 (p : Pattern) : Int := if p 116 then d4733 p else d4729 p
theorem agree4734 (p q : Pattern) (h : Agree support p q) : d4734 p = d4734 q := by
  simp only [d4734, h 116 (by decide), agree4733 p q h, agree4729 p q h]
theorem nonnegative4734 (p : Pattern) : 0 ≤ d4734 p :=
  nonnegative_ite (p 116) (nonnegative4733 p) (nonnegative4729 p)
def d4735 (p : Pattern) : Int := if p 115 then d4734 p else d4732 p
theorem agree4735 (p q : Pattern) (h : Agree support p q) : d4735 p = d4735 q := by
  simp only [d4735, h 115 (by decide), agree4734 p q h, agree4732 p q h]
theorem nonnegative4735 (p : Pattern) : 0 ≤ d4735 p :=
  nonnegative_ite (p 115) (nonnegative4734 p) (nonnegative4732 p)
def d4736 (p : Pattern) : Int := if p 141 then d138 p else d114 p
theorem agree4736 (p q : Pattern) (h : Agree support p q) : d4736 p = d4736 q := by
  simp only [d4736, h 141 (by decide), agree138 p q h, agree114 p q h]
theorem nonnegative4736 (p : Pattern) : 0 ≤ d4736 p :=
  nonnegative_ite (p 141) (nonnegative138 p) (nonnegative114 p)
def d4737 (p : Pattern) : Int := if p 141 then d12 p else d160 p
theorem agree4737 (p q : Pattern) (h : Agree support p q) : d4737 p = d4737 q := by
  simp only [d4737, h 141 (by decide), agree12 p q h, agree160 p q h]
theorem nonnegative4737 (p : Pattern) : 0 ≤ d4737 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative160 p)
def d4738 (p : Pattern) : Int := if p 138 then d4737 p else d4736 p
theorem agree4738 (p q : Pattern) (h : Agree support p q) : d4738 p = d4738 q := by
  simp only [d4738, h 138 (by decide), agree4737 p q h, agree4736 p q h]
theorem nonnegative4738 (p : Pattern) : 0 ≤ d4738 p :=
  nonnegative_ite (p 138) (nonnegative4737 p) (nonnegative4736 p)
def d4739 (p : Pattern) : Int := if p 116 then d4738 p else d4736 p
theorem agree4739 (p q : Pattern) (h : Agree support p q) : d4739 p = d4739 q := by
  simp only [d4739, h 116 (by decide), agree4738 p q h, agree4736 p q h]
theorem nonnegative4739 (p : Pattern) : 0 ≤ d4739 p :=
  nonnegative_ite (p 116) (nonnegative4738 p) (nonnegative4736 p)
def d4740 (p : Pattern) : Int := if p 138 then d12 p else d4736 p
theorem agree4740 (p q : Pattern) (h : Agree support p q) : d4740 p = d4740 q := by
  simp only [d4740, h 138 (by decide), agree12 p q h, agree4736 p q h]
theorem nonnegative4740 (p : Pattern) : 0 ≤ d4740 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4736 p)
def d4741 (p : Pattern) : Int := if p 116 then d4740 p else d4736 p
theorem agree4741 (p q : Pattern) (h : Agree support p q) : d4741 p = d4741 q := by
  simp only [d4741, h 116 (by decide), agree4740 p q h, agree4736 p q h]
theorem nonnegative4741 (p : Pattern) : 0 ≤ d4741 p :=
  nonnegative_ite (p 116) (nonnegative4740 p) (nonnegative4736 p)
def d4742 (p : Pattern) : Int := if p 115 then d4741 p else d4739 p
theorem agree4742 (p q : Pattern) (h : Agree support p q) : d4742 p = d4742 q := by
  simp only [d4742, h 115 (by decide), agree4741 p q h, agree4739 p q h]
theorem nonnegative4742 (p : Pattern) : 0 ≤ d4742 p :=
  nonnegative_ite (p 115) (nonnegative4741 p) (nonnegative4739 p)
def d4743 (p : Pattern) : Int := if p 71 then d4742 p else d4735 p
theorem agree4743 (p q : Pattern) (h : Agree support p q) : d4743 p = d4743 q := by
  simp only [d4743, h 71 (by decide), agree4742 p q h, agree4735 p q h]
theorem nonnegative4743 (p : Pattern) : 0 ≤ d4743 p :=
  nonnegative_ite (p 71) (nonnegative4742 p) (nonnegative4735 p)
def d4744 (p : Pattern) : Int := if p 49 then d4743 p else d4735 p
theorem agree4744 (p q : Pattern) (h : Agree support p q) : d4744 p = d4744 q := by
  simp only [d4744, h 49 (by decide), agree4743 p q h, agree4735 p q h]
theorem nonnegative4744 (p : Pattern) : 0 ≤ d4744 p :=
  nonnegative_ite (p 49) (nonnegative4743 p) (nonnegative4735 p)
def d4745 (p : Pattern) : Int := if p 141 then d200 p else d189 p
theorem agree4745 (p q : Pattern) (h : Agree support p q) : d4745 p = d4745 q := by
  simp only [d4745, h 141 (by decide), agree200 p q h, agree189 p q h]
theorem nonnegative4745 (p : Pattern) : 0 ≤ d4745 p :=
  nonnegative_ite (p 141) (nonnegative200 p) (nonnegative189 p)
def d4746 (p : Pattern) : Int := if p 138 then d4745 p else d4729 p
theorem agree4746 (p q : Pattern) (h : Agree support p q) : d4746 p = d4746 q := by
  simp only [d4746, h 138 (by decide), agree4745 p q h, agree4729 p q h]
theorem nonnegative4746 (p : Pattern) : 0 ≤ d4746 p :=
  nonnegative_ite (p 138) (nonnegative4745 p) (nonnegative4729 p)
def d4747 (p : Pattern) : Int := if p 138 then d12 p else d4745 p
theorem agree4747 (p q : Pattern) (h : Agree support p q) : d4747 p = d4747 q := by
  simp only [d4747, h 138 (by decide), agree12 p q h, agree4745 p q h]
theorem nonnegative4747 (p : Pattern) : 0 ≤ d4747 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4745 p)
def d4748 (p : Pattern) : Int := if p 116 then d4747 p else d4746 p
theorem agree4748 (p q : Pattern) (h : Agree support p q) : d4748 p = d4748 q := by
  simp only [d4748, h 116 (by decide), agree4747 p q h, agree4746 p q h]
theorem nonnegative4748 (p : Pattern) : 0 ≤ d4748 p :=
  nonnegative_ite (p 116) (nonnegative4747 p) (nonnegative4746 p)
def d4749 (p : Pattern) : Int := if p 115 then d4748 p else d4732 p
theorem agree4749 (p q : Pattern) (h : Agree support p q) : d4749 p = d4749 q := by
  simp only [d4749, h 115 (by decide), agree4748 p q h, agree4732 p q h]
theorem nonnegative4749 (p : Pattern) : 0 ≤ d4749 p :=
  nonnegative_ite (p 115) (nonnegative4748 p) (nonnegative4732 p)
def d4750 (p : Pattern) : Int := if p 71 then d4749 p else d4735 p
theorem agree4750 (p q : Pattern) (h : Agree support p q) : d4750 p = d4750 q := by
  simp only [d4750, h 71 (by decide), agree4749 p q h, agree4735 p q h]
theorem nonnegative4750 (p : Pattern) : 0 ≤ d4750 p :=
  nonnegative_ite (p 71) (nonnegative4749 p) (nonnegative4735 p)
def d4751 (p : Pattern) : Int := if p 141 then d214 p else d114 p
theorem agree4751 (p q : Pattern) (h : Agree support p q) : d4751 p = d4751 q := by
  simp only [d4751, h 141 (by decide), agree214 p q h, agree114 p q h]
theorem nonnegative4751 (p : Pattern) : 0 ≤ d4751 p :=
  nonnegative_ite (p 141) (nonnegative214 p) (nonnegative114 p)
def d4752 (p : Pattern) : Int := if p 138 then d4737 p else d4751 p
theorem agree4752 (p q : Pattern) (h : Agree support p q) : d4752 p = d4752 q := by
  simp only [d4752, h 138 (by decide), agree4737 p q h, agree4751 p q h]
theorem nonnegative4752 (p : Pattern) : 0 ≤ d4752 p :=
  nonnegative_ite (p 138) (nonnegative4737 p) (nonnegative4751 p)
def d4753 (p : Pattern) : Int := if p 116 then d4752 p else d4751 p
theorem agree4753 (p q : Pattern) (h : Agree support p q) : d4753 p = d4753 q := by
  simp only [d4753, h 116 (by decide), agree4752 p q h, agree4751 p q h]
theorem nonnegative4753 (p : Pattern) : 0 ≤ d4753 p :=
  nonnegative_ite (p 116) (nonnegative4752 p) (nonnegative4751 p)
def d4754 (p : Pattern) : Int := if p 141 then d246 p else d243 p
theorem agree4754 (p q : Pattern) (h : Agree support p q) : d4754 p = d4754 q := by
  simp only [d4754, h 141 (by decide), agree246 p q h, agree243 p q h]
theorem nonnegative4754 (p : Pattern) : 0 ≤ d4754 p :=
  nonnegative_ite (p 141) (nonnegative246 p) (nonnegative243 p)
def d4755 (p : Pattern) : Int := if p 138 then d4754 p else d4751 p
theorem agree4755 (p q : Pattern) (h : Agree support p q) : d4755 p = d4755 q := by
  simp only [d4755, h 138 (by decide), agree4754 p q h, agree4751 p q h]
theorem nonnegative4755 (p : Pattern) : 0 ≤ d4755 p :=
  nonnegative_ite (p 138) (nonnegative4754 p) (nonnegative4751 p)
def d4756 (p : Pattern) : Int := if p 141 then d246 p else d256 p
theorem agree4756 (p q : Pattern) (h : Agree support p q) : d4756 p = d4756 q := by
  simp only [d4756, h 141 (by decide), agree246 p q h, agree256 p q h]
theorem nonnegative4756 (p : Pattern) : 0 ≤ d4756 p :=
  nonnegative_ite (p 141) (nonnegative246 p) (nonnegative256 p)
def d4757 (p : Pattern) : Int := if p 138 then d12 p else d4756 p
theorem agree4757 (p q : Pattern) (h : Agree support p q) : d4757 p = d4757 q := by
  simp only [d4757, h 138 (by decide), agree12 p q h, agree4756 p q h]
theorem nonnegative4757 (p : Pattern) : 0 ≤ d4757 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4756 p)
def d4758 (p : Pattern) : Int := if p 116 then d4757 p else d4755 p
theorem agree4758 (p q : Pattern) (h : Agree support p q) : d4758 p = d4758 q := by
  simp only [d4758, h 116 (by decide), agree4757 p q h, agree4755 p q h]
theorem nonnegative4758 (p : Pattern) : 0 ≤ d4758 p :=
  nonnegative_ite (p 116) (nonnegative4757 p) (nonnegative4755 p)
def d4759 (p : Pattern) : Int := if p 115 then d4758 p else d4753 p
theorem agree4759 (p q : Pattern) (h : Agree support p q) : d4759 p = d4759 q := by
  simp only [d4759, h 115 (by decide), agree4758 p q h, agree4753 p q h]
theorem nonnegative4759 (p : Pattern) : 0 ≤ d4759 p :=
  nonnegative_ite (p 115) (nonnegative4758 p) (nonnegative4753 p)
def d4760 (p : Pattern) : Int := if p 71 then d4759 p else d4735 p
theorem agree4760 (p q : Pattern) (h : Agree support p q) : d4760 p = d4760 q := by
  simp only [d4760, h 71 (by decide), agree4759 p q h, agree4735 p q h]
theorem nonnegative4760 (p : Pattern) : 0 ≤ d4760 p :=
  nonnegative_ite (p 71) (nonnegative4759 p) (nonnegative4735 p)
def d4761 (p : Pattern) : Int := if p 49 then d4760 p else d4750 p
theorem agree4761 (p q : Pattern) (h : Agree support p q) : d4761 p = d4761 q := by
  simp only [d4761, h 49 (by decide), agree4760 p q h, agree4750 p q h]
theorem nonnegative4761 (p : Pattern) : 0 ≤ d4761 p :=
  nonnegative_ite (p 49) (nonnegative4760 p) (nonnegative4750 p)
def d4762 (p : Pattern) : Int := if p 48 then d4761 p else d4744 p
theorem agree4762 (p q : Pattern) (h : Agree support p q) : d4762 p = d4762 q := by
  simp only [d4762, h 48 (by decide), agree4761 p q h, agree4744 p q h]
theorem nonnegative4762 (p : Pattern) : 0 ≤ d4762 p :=
  nonnegative_ite (p 48) (nonnegative4761 p) (nonnegative4744 p)
def d4763 (p : Pattern) : Int := if p 161 then d0 p else d4206 p
theorem agree4763 (p q : Pattern) (h : Agree support p q) : d4763 p = d4763 q := by
  simp only [d4763, h 161 (by decide), agree0 p q h, agree4206 p q h]
theorem nonnegative4763 (p : Pattern) : 0 ≤ d4763 p :=
  nonnegative_ite (p 161) (nonnegative0 p) (nonnegative4206 p)
def d4764 (p : Pattern) : Int := if p 160 then d0 p else d4763 p
theorem agree4764 (p q : Pattern) (h : Agree support p q) : d4764 p = d4764 q := by
  simp only [d4764, h 160 (by decide), agree0 p q h, agree4763 p q h]
theorem nonnegative4764 (p : Pattern) : 0 ≤ d4764 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative4763 p)
def d4765 (p : Pattern) : Int := if p 162 then d0 p else d4147 p
theorem agree4765 (p q : Pattern) (h : Agree support p q) : d4765 p = d4765 q := by
  simp only [d4765, h 162 (by decide), agree0 p q h, agree4147 p q h]
theorem nonnegative4765 (p : Pattern) : 0 ≤ d4765 p :=
  nonnegative_ite (p 162) (nonnegative0 p) (nonnegative4147 p)
def d4766 (p : Pattern) : Int := if p 141 then d799 p else d791 p
theorem agree4766 (p q : Pattern) (h : Agree support p q) : d4766 p = d4766 q := by
  simp only [d4766, h 141 (by decide), agree799 p q h, agree791 p q h]
theorem nonnegative4766 (p : Pattern) : 0 ≤ d4766 p :=
  nonnegative_ite (p 141) (nonnegative799 p) (nonnegative791 p)
def d4767 (p : Pattern) : Int := if p 141 then d810 p else d804 p
theorem agree4767 (p q : Pattern) (h : Agree support p q) : d4767 p = d4767 q := by
  simp only [d4767, h 141 (by decide), agree810 p q h, agree804 p q h]
theorem nonnegative4767 (p : Pattern) : 0 ≤ d4767 p :=
  nonnegative_ite (p 141) (nonnegative810 p) (nonnegative804 p)
def d4768 (p : Pattern) : Int := if p 138 then d4767 p else d4766 p
theorem agree4768 (p q : Pattern) (h : Agree support p q) : d4768 p = d4768 q := by
  simp only [d4768, h 138 (by decide), agree4767 p q h, agree4766 p q h]
theorem nonnegative4768 (p : Pattern) : 0 ≤ d4768 p :=
  nonnegative_ite (p 138) (nonnegative4767 p) (nonnegative4766 p)
def d4769 (p : Pattern) : Int := if p 138 then d4434 p else d4767 p
theorem agree4769 (p q : Pattern) (h : Agree support p q) : d4769 p = d4769 q := by
  simp only [d4769, h 138 (by decide), agree4434 p q h, agree4767 p q h]
theorem nonnegative4769 (p : Pattern) : 0 ≤ d4769 p :=
  nonnegative_ite (p 138) (nonnegative4434 p) (nonnegative4767 p)
def d4770 (p : Pattern) : Int := if p 116 then d4769 p else d4768 p
theorem agree4770 (p q : Pattern) (h : Agree support p q) : d4770 p = d4770 q := by
  simp only [d4770, h 116 (by decide), agree4769 p q h, agree4768 p q h]
theorem nonnegative4770 (p : Pattern) : 0 ≤ d4770 p :=
  nonnegative_ite (p 116) (nonnegative4769 p) (nonnegative4768 p)
def d4771 (p : Pattern) : Int := if p 138 then d12 p else d4767 p
theorem agree4771 (p q : Pattern) (h : Agree support p q) : d4771 p = d4771 q := by
  simp only [d4771, h 138 (by decide), agree12 p q h, agree4767 p q h]
theorem nonnegative4771 (p : Pattern) : 0 ≤ d4771 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4767 p)
def d4772 (p : Pattern) : Int := if p 116 then d4771 p else d4768 p
theorem agree4772 (p q : Pattern) (h : Agree support p q) : d4772 p = d4772 q := by
  simp only [d4772, h 116 (by decide), agree4771 p q h, agree4768 p q h]
theorem nonnegative4772 (p : Pattern) : 0 ≤ d4772 p :=
  nonnegative_ite (p 116) (nonnegative4771 p) (nonnegative4768 p)
def d4773 (p : Pattern) : Int := if p 115 then d4772 p else d4770 p
theorem agree4773 (p q : Pattern) (h : Agree support p q) : d4773 p = d4773 q := by
  simp only [d4773, h 115 (by decide), agree4772 p q h, agree4770 p q h]
theorem nonnegative4773 (p : Pattern) : 0 ≤ d4773 p :=
  nonnegative_ite (p 115) (nonnegative4772 p) (nonnegative4770 p)
def d4774 (p : Pattern) : Int := if p 141 then d864 p else d857 p
theorem agree4774 (p q : Pattern) (h : Agree support p q) : d4774 p = d4774 q := by
  simp only [d4774, h 141 (by decide), agree864 p q h, agree857 p q h]
theorem nonnegative4774 (p : Pattern) : 0 ≤ d4774 p :=
  nonnegative_ite (p 141) (nonnegative864 p) (nonnegative857 p)
def d4775 (p : Pattern) : Int := if p 141 then d874 p else d869 p
theorem agree4775 (p q : Pattern) (h : Agree support p q) : d4775 p = d4775 q := by
  simp only [d4775, h 141 (by decide), agree874 p q h, agree869 p q h]
theorem nonnegative4775 (p : Pattern) : 0 ≤ d4775 p :=
  nonnegative_ite (p 141) (nonnegative874 p) (nonnegative869 p)
def d4776 (p : Pattern) : Int := if p 138 then d4775 p else d4774 p
theorem agree4776 (p q : Pattern) (h : Agree support p q) : d4776 p = d4776 q := by
  simp only [d4776, h 138 (by decide), agree4775 p q h, agree4774 p q h]
theorem nonnegative4776 (p : Pattern) : 0 ≤ d4776 p :=
  nonnegative_ite (p 138) (nonnegative4775 p) (nonnegative4774 p)
def d4777 (p : Pattern) : Int := if p 138 then d12 p else d4775 p
theorem agree4777 (p q : Pattern) (h : Agree support p q) : d4777 p = d4777 q := by
  simp only [d4777, h 138 (by decide), agree12 p q h, agree4775 p q h]
theorem nonnegative4777 (p : Pattern) : 0 ≤ d4777 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4775 p)
def d4778 (p : Pattern) : Int := if p 116 then d4777 p else d4776 p
theorem agree4778 (p q : Pattern) (h : Agree support p q) : d4778 p = d4778 q := by
  simp only [d4778, h 116 (by decide), agree4777 p q h, agree4776 p q h]
theorem nonnegative4778 (p : Pattern) : 0 ≤ d4778 p :=
  nonnegative_ite (p 116) (nonnegative4777 p) (nonnegative4776 p)
def d4779 (p : Pattern) : Int := if p 71 then d4778 p else d4773 p
theorem agree4779 (p q : Pattern) (h : Agree support p q) : d4779 p = d4779 q := by
  simp only [d4779, h 71 (by decide), agree4778 p q h, agree4773 p q h]
theorem nonnegative4779 (p : Pattern) : 0 ≤ d4779 p :=
  nonnegative_ite (p 71) (nonnegative4778 p) (nonnegative4773 p)
def d4780 (p : Pattern) : Int := if p 49 then d4779 p else d4773 p
theorem agree4780 (p q : Pattern) (h : Agree support p q) : d4780 p = d4780 q := by
  simp only [d4780, h 49 (by decide), agree4779 p q h, agree4773 p q h]
theorem nonnegative4780 (p : Pattern) : 0 ≤ d4780 p :=
  nonnegative_ite (p 49) (nonnegative4779 p) (nonnegative4773 p)
def d4781 (p : Pattern) : Int := if p 141 then d903 p else d899 p
theorem agree4781 (p q : Pattern) (h : Agree support p q) : d4781 p = d4781 q := by
  simp only [d4781, h 141 (by decide), agree903 p q h, agree899 p q h]
theorem nonnegative4781 (p : Pattern) : 0 ≤ d4781 p :=
  nonnegative_ite (p 141) (nonnegative903 p) (nonnegative899 p)
def d4782 (p : Pattern) : Int := if p 138 then d4781 p else d4766 p
theorem agree4782 (p q : Pattern) (h : Agree support p q) : d4782 p = d4782 q := by
  simp only [d4782, h 138 (by decide), agree4781 p q h, agree4766 p q h]
theorem nonnegative4782 (p : Pattern) : 0 ≤ d4782 p :=
  nonnegative_ite (p 138) (nonnegative4781 p) (nonnegative4766 p)
def d4783 (p : Pattern) : Int := if p 138 then d12 p else d4781 p
theorem agree4783 (p q : Pattern) (h : Agree support p q) : d4783 p = d4783 q := by
  simp only [d4783, h 138 (by decide), agree12 p q h, agree4781 p q h]
theorem nonnegative4783 (p : Pattern) : 0 ≤ d4783 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4781 p)
def d4784 (p : Pattern) : Int := if p 116 then d4783 p else d4782 p
theorem agree4784 (p q : Pattern) (h : Agree support p q) : d4784 p = d4784 q := by
  simp only [d4784, h 116 (by decide), agree4783 p q h, agree4782 p q h]
theorem nonnegative4784 (p : Pattern) : 0 ≤ d4784 p :=
  nonnegative_ite (p 116) (nonnegative4783 p) (nonnegative4782 p)
def d4785 (p : Pattern) : Int := if p 115 then d4784 p else d4770 p
theorem agree4785 (p q : Pattern) (h : Agree support p q) : d4785 p = d4785 q := by
  simp only [d4785, h 115 (by decide), agree4784 p q h, agree4770 p q h]
theorem nonnegative4785 (p : Pattern) : 0 ≤ d4785 p :=
  nonnegative_ite (p 115) (nonnegative4784 p) (nonnegative4770 p)
def d4786 (p : Pattern) : Int := if p 71 then d4785 p else d4773 p
theorem agree4786 (p q : Pattern) (h : Agree support p q) : d4786 p = d4786 q := by
  simp only [d4786, h 71 (by decide), agree4785 p q h, agree4773 p q h]
theorem nonnegative4786 (p : Pattern) : 0 ≤ d4786 p :=
  nonnegative_ite (p 71) (nonnegative4785 p) (nonnegative4773 p)
def d4787 (p : Pattern) : Int := if p 141 then d926 p else d922 p
theorem agree4787 (p q : Pattern) (h : Agree support p q) : d4787 p = d4787 q := by
  simp only [d4787, h 141 (by decide), agree926 p q h, agree922 p q h]
theorem nonnegative4787 (p : Pattern) : 0 ≤ d4787 p :=
  nonnegative_ite (p 141) (nonnegative926 p) (nonnegative922 p)
def d4788 (p : Pattern) : Int := if p 141 then d933 p else d245 p
theorem agree4788 (p q : Pattern) (h : Agree support p q) : d4788 p = d4788 q := by
  simp only [d4788, h 141 (by decide), agree933 p q h, agree245 p q h]
theorem nonnegative4788 (p : Pattern) : 0 ≤ d4788 p :=
  nonnegative_ite (p 141) (nonnegative933 p) (nonnegative245 p)
def d4789 (p : Pattern) : Int := if p 138 then d4788 p else d4787 p
theorem agree4789 (p q : Pattern) (h : Agree support p q) : d4789 p = d4789 q := by
  simp only [d4789, h 138 (by decide), agree4788 p q h, agree4787 p q h]
theorem nonnegative4789 (p : Pattern) : 0 ≤ d4789 p :=
  nonnegative_ite (p 138) (nonnegative4788 p) (nonnegative4787 p)
def d4790 (p : Pattern) : Int := if p 141 then d933 p else d939 p
theorem agree4790 (p q : Pattern) (h : Agree support p q) : d4790 p = d4790 q := by
  simp only [d4790, h 141 (by decide), agree933 p q h, agree939 p q h]
theorem nonnegative4790 (p : Pattern) : 0 ≤ d4790 p :=
  nonnegative_ite (p 141) (nonnegative933 p) (nonnegative939 p)
def d4791 (p : Pattern) : Int := if p 138 then d12 p else d4790 p
theorem agree4791 (p q : Pattern) (h : Agree support p q) : d4791 p = d4791 q := by
  simp only [d4791, h 138 (by decide), agree12 p q h, agree4790 p q h]
theorem nonnegative4791 (p : Pattern) : 0 ≤ d4791 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4790 p)
def d4792 (p : Pattern) : Int := if p 116 then d4791 p else d4789 p
theorem agree4792 (p q : Pattern) (h : Agree support p q) : d4792 p = d4792 q := by
  simp only [d4792, h 116 (by decide), agree4791 p q h, agree4789 p q h]
theorem nonnegative4792 (p : Pattern) : 0 ≤ d4792 p :=
  nonnegative_ite (p 116) (nonnegative4791 p) (nonnegative4789 p)
def d4793 (p : Pattern) : Int := if p 115 then d4792 p else d4778 p
theorem agree4793 (p q : Pattern) (h : Agree support p q) : d4793 p = d4793 q := by
  simp only [d4793, h 115 (by decide), agree4792 p q h, agree4778 p q h]
theorem nonnegative4793 (p : Pattern) : 0 ≤ d4793 p :=
  nonnegative_ite (p 115) (nonnegative4792 p) (nonnegative4778 p)
def d4794 (p : Pattern) : Int := if p 71 then d4793 p else d4773 p
theorem agree4794 (p q : Pattern) (h : Agree support p q) : d4794 p = d4794 q := by
  simp only [d4794, h 71 (by decide), agree4793 p q h, agree4773 p q h]
theorem nonnegative4794 (p : Pattern) : 0 ≤ d4794 p :=
  nonnegative_ite (p 71) (nonnegative4793 p) (nonnegative4773 p)
def d4795 (p : Pattern) : Int := if p 49 then d4794 p else d4786 p
theorem agree4795 (p q : Pattern) (h : Agree support p q) : d4795 p = d4795 q := by
  simp only [d4795, h 49 (by decide), agree4794 p q h, agree4786 p q h]
theorem nonnegative4795 (p : Pattern) : 0 ≤ d4795 p :=
  nonnegative_ite (p 49) (nonnegative4794 p) (nonnegative4786 p)
def d4796 (p : Pattern) : Int := if p 48 then d4795 p else d4780 p
theorem agree4796 (p q : Pattern) (h : Agree support p q) : d4796 p = d4796 q := by
  simp only [d4796, h 48 (by decide), agree4795 p q h, agree4780 p q h]
theorem nonnegative4796 (p : Pattern) : 0 ≤ d4796 p :=
  nonnegative_ite (p 48) (nonnegative4795 p) (nonnegative4780 p)
def d4797 (p : Pattern) : Int := if p 138 then d82 p else d52 p
theorem agree4797 (p q : Pattern) (h : Agree support p q) : d4797 p = d4797 q := by
  simp only [d4797, h 138 (by decide), agree82 p q h, agree52 p q h]
theorem nonnegative4797 (p : Pattern) : 0 ≤ d4797 p :=
  nonnegative_ite (p 138) (nonnegative82 p) (nonnegative52 p)
def d4798 (p : Pattern) : Int := if p 138 then d94 p else d82 p
theorem agree4798 (p q : Pattern) (h : Agree support p q) : d4798 p = d4798 q := by
  simp only [d4798, h 138 (by decide), agree94 p q h, agree82 p q h]
theorem nonnegative4798 (p : Pattern) : 0 ≤ d4798 p :=
  nonnegative_ite (p 138) (nonnegative94 p) (nonnegative82 p)
def d4799 (p : Pattern) : Int := if p 116 then d4798 p else d4797 p
theorem agree4799 (p q : Pattern) (h : Agree support p q) : d4799 p = d4799 q := by
  simp only [d4799, h 116 (by decide), agree4798 p q h, agree4797 p q h]
theorem nonnegative4799 (p : Pattern) : 0 ≤ d4799 p :=
  nonnegative_ite (p 116) (nonnegative4798 p) (nonnegative4797 p)
end NetHack.Sokoban22Refined85
