/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes63
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7680 (p : Pattern) : Int := if p 204 then d7679 p else d3244 p
theorem agree7680 (p q : Pattern) (h : Agree support p q) : d7680 p = d7680 q := by
  simp only [d7680, h 204 (by decide), agree7679 p q h, agree3244 p q h]
theorem nonnegative7680 (p : Pattern) : 0 ≤ d7680 p :=
  nonnegative_ite (p 204) (nonnegative7679 p) (nonnegative3244 p)
def d7681 (p : Pattern) : Int := if p 225 then d3257 p else d3244 p
theorem agree7681 (p q : Pattern) (h : Agree support p q) : d7681 p = d7681 q := by
  simp only [d7681, h 225 (by decide), agree3257 p q h, agree3244 p q h]
theorem nonnegative7681 (p : Pattern) : 0 ≤ d7681 p :=
  nonnegative_ite (p 225) (nonnegative3257 p) (nonnegative3244 p)
def d7682 (p : Pattern) : Int := if p 224 then d3257 p else d7681 p
theorem agree7682 (p q : Pattern) (h : Agree support p q) : d7682 p = d7682 q := by
  simp only [d7682, h 224 (by decide), agree3257 p q h, agree7681 p q h]
theorem nonnegative7682 (p : Pattern) : 0 ≤ d7682 p :=
  nonnegative_ite (p 224) (nonnegative3257 p) (nonnegative7681 p)
def d7683 (p : Pattern) : Int := if p 204 then d12 p else d7682 p
theorem agree7683 (p q : Pattern) (h : Agree support p q) : d7683 p = d7683 q := by
  simp only [d7683, h 204 (by decide), agree12 p q h, agree7682 p q h]
theorem nonnegative7683 (p : Pattern) : 0 ≤ d7683 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7682 p)
def d7684 (p : Pattern) : Int := if p 182 then d7683 p else d7680 p
theorem agree7684 (p q : Pattern) (h : Agree support p q) : d7684 p = d7684 q := by
  simp only [d7684, h 182 (by decide), agree7683 p q h, agree7680 p q h]
theorem nonnegative7684 (p : Pattern) : 0 ≤ d7684 p :=
  nonnegative_ite (p 182) (nonnegative7683 p) (nonnegative7680 p)
def d7685 (p : Pattern) : Int := if p 163 then d12 p else d7684 p
theorem agree7685 (p q : Pattern) (h : Agree support p q) : d7685 p = d7685 q := by
  simp only [d7685, h 163 (by decide), agree12 p q h, agree7684 p q h]
theorem nonnegative7685 (p : Pattern) : 0 ≤ d7685 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7684 p)
def d7686 (p : Pattern) : Int := if p 162 then d7685 p else d7676 p
theorem agree7686 (p q : Pattern) (h : Agree support p q) : d7686 p = d7686 q := by
  simp only [d7686, h 162 (by decide), agree7685 p q h, agree7676 p q h]
theorem nonnegative7686 (p : Pattern) : 0 ≤ d7686 p :=
  nonnegative_ite (p 162) (nonnegative7685 p) (nonnegative7676 p)
def d7687 (p : Pattern) : Int := if p 161 then d7686 p else d7677 p
theorem agree7687 (p q : Pattern) (h : Agree support p q) : d7687 p = d7687 q := by
  simp only [d7687, h 161 (by decide), agree7686 p q h, agree7677 p q h]
theorem nonnegative7687 (p : Pattern) : 0 ≤ d7687 p :=
  nonnegative_ite (p 161) (nonnegative7686 p) (nonnegative7677 p)
def d7688 (p : Pattern) : Int := if p 225 then d3253 p else d3226 p
theorem agree7688 (p q : Pattern) (h : Agree support p q) : d7688 p = d7688 q := by
  simp only [d7688, h 225 (by decide), agree3253 p q h, agree3226 p q h]
theorem nonnegative7688 (p : Pattern) : 0 ≤ d7688 p :=
  nonnegative_ite (p 225) (nonnegative3253 p) (nonnegative3226 p)
def d7689 (p : Pattern) : Int := if p 225 then d3257 p else d3239 p
theorem agree7689 (p q : Pattern) (h : Agree support p q) : d7689 p = d7689 q := by
  simp only [d7689, h 225 (by decide), agree3257 p q h, agree3239 p q h]
theorem nonnegative7689 (p : Pattern) : 0 ≤ d7689 p :=
  nonnegative_ite (p 225) (nonnegative3257 p) (nonnegative3239 p)
def d7690 (p : Pattern) : Int := if p 224 then d7689 p else d7688 p
theorem agree7690 (p q : Pattern) (h : Agree support p q) : d7690 p = d7690 q := by
  simp only [d7690, h 224 (by decide), agree7689 p q h, agree7688 p q h]
theorem nonnegative7690 (p : Pattern) : 0 ≤ d7690 p :=
  nonnegative_ite (p 224) (nonnegative7689 p) (nonnegative7688 p)
def d7691 (p : Pattern) : Int := if p 204 then d7690 p else d3226 p
theorem agree7691 (p q : Pattern) (h : Agree support p q) : d7691 p = d7691 q := by
  simp only [d7691, h 204 (by decide), agree7690 p q h, agree3226 p q h]
theorem nonnegative7691 (p : Pattern) : 0 ≤ d7691 p :=
  nonnegative_ite (p 204) (nonnegative7690 p) (nonnegative3226 p)
def d7692 (p : Pattern) : Int := if p 225 then d3461 p else d3250 p
theorem agree7692 (p q : Pattern) (h : Agree support p q) : d7692 p = d7692 q := by
  simp only [d7692, h 225 (by decide), agree3461 p q h, agree3250 p q h]
theorem nonnegative7692 (p : Pattern) : 0 ≤ d7692 p :=
  nonnegative_ite (p 225) (nonnegative3461 p) (nonnegative3250 p)
def d7693 (p : Pattern) : Int := if p 225 then d12 p else d3253 p
theorem agree7693 (p q : Pattern) (h : Agree support p q) : d7693 p = d7693 q := by
  simp only [d7693, h 225 (by decide), agree12 p q h, agree3253 p q h]
theorem nonnegative7693 (p : Pattern) : 0 ≤ d7693 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative3253 p)
def d7694 (p : Pattern) : Int := if p 224 then d7693 p else d7692 p
theorem agree7694 (p q : Pattern) (h : Agree support p q) : d7694 p = d7694 q := by
  simp only [d7694, h 224 (by decide), agree7693 p q h, agree7692 p q h]
theorem nonnegative7694 (p : Pattern) : 0 ≤ d7694 p :=
  nonnegative_ite (p 224) (nonnegative7693 p) (nonnegative7692 p)
def d7695 (p : Pattern) : Int := if p 204 then d12 p else d7694 p
theorem agree7695 (p q : Pattern) (h : Agree support p q) : d7695 p = d7695 q := by
  simp only [d7695, h 204 (by decide), agree12 p q h, agree7694 p q h]
theorem nonnegative7695 (p : Pattern) : 0 ≤ d7695 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7694 p)
def d7696 (p : Pattern) : Int := if p 182 then d7695 p else d7691 p
theorem agree7696 (p q : Pattern) (h : Agree support p q) : d7696 p = d7696 q := by
  simp only [d7696, h 182 (by decide), agree7695 p q h, agree7691 p q h]
theorem nonnegative7696 (p : Pattern) : 0 ≤ d7696 p :=
  nonnegative_ite (p 182) (nonnegative7695 p) (nonnegative7691 p)
def d7697 (p : Pattern) : Int := if p 225 then d12 p else d3279 p
theorem agree7697 (p q : Pattern) (h : Agree support p q) : d7697 p = d7697 q := by
  simp only [d7697, h 225 (by decide), agree12 p q h, agree3279 p q h]
theorem nonnegative7697 (p : Pattern) : 0 ≤ d7697 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative3279 p)
def d7698 (p : Pattern) : Int := if p 224 then d7697 p else d7693 p
theorem agree7698 (p q : Pattern) (h : Agree support p q) : d7698 p = d7698 q := by
  simp only [d7698, h 224 (by decide), agree7697 p q h, agree7693 p q h]
theorem nonnegative7698 (p : Pattern) : 0 ≤ d7698 p :=
  nonnegative_ite (p 224) (nonnegative7697 p) (nonnegative7693 p)
def d7699 (p : Pattern) : Int := if p 204 then d12 p else d7698 p
theorem agree7699 (p q : Pattern) (h : Agree support p q) : d7699 p = d7699 q := by
  simp only [d7699, h 204 (by decide), agree12 p q h, agree7698 p q h]
theorem nonnegative7699 (p : Pattern) : 0 ≤ d7699 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7698 p)
def d7700 (p : Pattern) : Int := if p 182 then d7699 p else d7691 p
theorem agree7700 (p q : Pattern) (h : Agree support p q) : d7700 p = d7700 q := by
  simp only [d7700, h 182 (by decide), agree7699 p q h, agree7691 p q h]
theorem nonnegative7700 (p : Pattern) : 0 ≤ d7700 p :=
  nonnegative_ite (p 182) (nonnegative7699 p) (nonnegative7691 p)
def d7701 (p : Pattern) : Int := if p 163 then d7700 p else d7696 p
theorem agree7701 (p q : Pattern) (h : Agree support p q) : d7701 p = d7701 q := by
  simp only [d7701, h 163 (by decide), agree7700 p q h, agree7696 p q h]
theorem nonnegative7701 (p : Pattern) : 0 ≤ d7701 p :=
  nonnegative_ite (p 163) (nonnegative7700 p) (nonnegative7696 p)
def d7702 (p : Pattern) : Int := if p 225 then d12 p else d3257 p
theorem agree7702 (p q : Pattern) (h : Agree support p q) : d7702 p = d7702 q := by
  simp only [d7702, h 225 (by decide), agree12 p q h, agree3257 p q h]
theorem nonnegative7702 (p : Pattern) : 0 ≤ d7702 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative3257 p)
def d7703 (p : Pattern) : Int := if p 224 then d12 p else d7702 p
theorem agree7703 (p q : Pattern) (h : Agree support p q) : d7703 p = d7703 q := by
  simp only [d7703, h 224 (by decide), agree12 p q h, agree7702 p q h]
theorem nonnegative7703 (p : Pattern) : 0 ≤ d7703 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7702 p)
def d7704 (p : Pattern) : Int := if p 204 then d12 p else d7703 p
theorem agree7704 (p q : Pattern) (h : Agree support p q) : d7704 p = d7704 q := by
  simp only [d7704, h 204 (by decide), agree12 p q h, agree7703 p q h]
theorem nonnegative7704 (p : Pattern) : 0 ≤ d7704 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7703 p)
def d7705 (p : Pattern) : Int := if p 182 then d7704 p else d7691 p
theorem agree7705 (p q : Pattern) (h : Agree support p q) : d7705 p = d7705 q := by
  simp only [d7705, h 182 (by decide), agree7704 p q h, agree7691 p q h]
theorem nonnegative7705 (p : Pattern) : 0 ≤ d7705 p :=
  nonnegative_ite (p 182) (nonnegative7704 p) (nonnegative7691 p)
def d7706 (p : Pattern) : Int := if p 225 then d3279 p else d3239 p
theorem agree7706 (p q : Pattern) (h : Agree support p q) : d7706 p = d7706 q := by
  simp only [d7706, h 225 (by decide), agree3279 p q h, agree3239 p q h]
theorem nonnegative7706 (p : Pattern) : 0 ≤ d7706 p :=
  nonnegative_ite (p 225) (nonnegative3279 p) (nonnegative3239 p)
def d7707 (p : Pattern) : Int := if p 225 then d12 p else d3461 p
theorem agree7707 (p q : Pattern) (h : Agree support p q) : d7707 p = d7707 q := by
  simp only [d7707, h 225 (by decide), agree12 p q h, agree3461 p q h]
theorem nonnegative7707 (p : Pattern) : 0 ≤ d7707 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative3461 p)
def d7708 (p : Pattern) : Int := if p 224 then d7707 p else d7706 p
theorem agree7708 (p q : Pattern) (h : Agree support p q) : d7708 p = d7708 q := by
  simp only [d7708, h 224 (by decide), agree7707 p q h, agree7706 p q h]
theorem nonnegative7708 (p : Pattern) : 0 ≤ d7708 p :=
  nonnegative_ite (p 224) (nonnegative7707 p) (nonnegative7706 p)
def d7709 (p : Pattern) : Int := if p 204 then d7708 p else d3239 p
theorem agree7709 (p q : Pattern) (h : Agree support p q) : d7709 p = d7709 q := by
  simp only [d7709, h 204 (by decide), agree7708 p q h, agree3239 p q h]
theorem nonnegative7709 (p : Pattern) : 0 ≤ d7709 p :=
  nonnegative_ite (p 204) (nonnegative7708 p) (nonnegative3239 p)
def d7710 (p : Pattern) : Int := if p 182 then d12 p else d7709 p
theorem agree7710 (p q : Pattern) (h : Agree support p q) : d7710 p = d7710 q := by
  simp only [d7710, h 182 (by decide), agree12 p q h, agree7709 p q h]
theorem nonnegative7710 (p : Pattern) : 0 ≤ d7710 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7709 p)
def d7711 (p : Pattern) : Int := if p 163 then d7710 p else d7705 p
theorem agree7711 (p q : Pattern) (h : Agree support p q) : d7711 p = d7711 q := by
  simp only [d7711, h 163 (by decide), agree7710 p q h, agree7705 p q h]
theorem nonnegative7711 (p : Pattern) : 0 ≤ d7711 p :=
  nonnegative_ite (p 163) (nonnegative7710 p) (nonnegative7705 p)
def d7712 (p : Pattern) : Int := if p 162 then d7711 p else d7701 p
theorem agree7712 (p q : Pattern) (h : Agree support p q) : d7712 p = d7712 q := by
  simp only [d7712, h 162 (by decide), agree7711 p q h, agree7701 p q h]
theorem nonnegative7712 (p : Pattern) : 0 ≤ d7712 p :=
  nonnegative_ite (p 162) (nonnegative7711 p) (nonnegative7701 p)
def d7713 (p : Pattern) : Int := if p 182 then d12 p else d7691 p
theorem agree7713 (p q : Pattern) (h : Agree support p q) : d7713 p = d7713 q := by
  simp only [d7713, h 182 (by decide), agree12 p q h, agree7691 p q h]
theorem nonnegative7713 (p : Pattern) : 0 ≤ d7713 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7691 p)
def d7714 (p : Pattern) : Int := if p 163 then d7710 p else d7713 p
theorem agree7714 (p q : Pattern) (h : Agree support p q) : d7714 p = d7714 q := by
  simp only [d7714, h 163 (by decide), agree7710 p q h, agree7713 p q h]
theorem nonnegative7714 (p : Pattern) : 0 ≤ d7714 p :=
  nonnegative_ite (p 163) (nonnegative7710 p) (nonnegative7713 p)
def d7715 (p : Pattern) : Int := if p 182 then d12 p else d7680 p
theorem agree7715 (p q : Pattern) (h : Agree support p q) : d7715 p = d7715 q := by
  simp only [d7715, h 182 (by decide), agree12 p q h, agree7680 p q h]
theorem nonnegative7715 (p : Pattern) : 0 ≤ d7715 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7680 p)
def d7716 (p : Pattern) : Int := if p 163 then d12 p else d7715 p
theorem agree7716 (p q : Pattern) (h : Agree support p q) : d7716 p = d7716 q := by
  simp only [d7716, h 163 (by decide), agree12 p q h, agree7715 p q h]
theorem nonnegative7716 (p : Pattern) : 0 ≤ d7716 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7715 p)
def d7717 (p : Pattern) : Int := if p 162 then d7716 p else d7714 p
theorem agree7717 (p q : Pattern) (h : Agree support p q) : d7717 p = d7717 q := by
  simp only [d7717, h 162 (by decide), agree7716 p q h, agree7714 p q h]
theorem nonnegative7717 (p : Pattern) : 0 ≤ d7717 p :=
  nonnegative_ite (p 162) (nonnegative7716 p) (nonnegative7714 p)
def d7718 (p : Pattern) : Int := if p 161 then d7717 p else d7712 p
theorem agree7718 (p q : Pattern) (h : Agree support p q) : d7718 p = d7718 q := by
  simp only [d7718, h 161 (by decide), agree7717 p q h, agree7712 p q h]
theorem nonnegative7718 (p : Pattern) : 0 ≤ d7718 p :=
  nonnegative_ite (p 161) (nonnegative7717 p) (nonnegative7712 p)
def d7719 (p : Pattern) : Int := if p 160 then d7718 p else d7687 p
theorem agree7719 (p q : Pattern) (h : Agree support p q) : d7719 p = d7719 q := by
  simp only [d7719, h 160 (by decide), agree7718 p q h, agree7687 p q h]
theorem nonnegative7719 (p : Pattern) : 0 ≤ d7719 p :=
  nonnegative_ite (p 160) (nonnegative7718 p) (nonnegative7687 p)
def d7720 (p : Pattern) : Int := if p 225 then d3253 p else d3250 p
theorem agree7720 (p q : Pattern) (h : Agree support p q) : d7720 p = d7720 q := by
  simp only [d7720, h 225 (by decide), agree3253 p q h, agree3250 p q h]
theorem nonnegative7720 (p : Pattern) : 0 ≤ d7720 p :=
  nonnegative_ite (p 225) (nonnegative3253 p) (nonnegative3250 p)
def d7721 (p : Pattern) : Int := if p 224 then d3253 p else d7720 p
theorem agree7721 (p q : Pattern) (h : Agree support p q) : d7721 p = d7721 q := by
  simp only [d7721, h 224 (by decide), agree3253 p q h, agree7720 p q h]
theorem nonnegative7721 (p : Pattern) : 0 ≤ d7721 p :=
  nonnegative_ite (p 224) (nonnegative3253 p) (nonnegative7720 p)
def d7722 (p : Pattern) : Int := if p 204 then d7721 p else d3250 p
theorem agree7722 (p q : Pattern) (h : Agree support p q) : d7722 p = d7722 q := by
  simp only [d7722, h 204 (by decide), agree7721 p q h, agree3250 p q h]
theorem nonnegative7722 (p : Pattern) : 0 ≤ d7722 p :=
  nonnegative_ite (p 204) (nonnegative7721 p) (nonnegative3250 p)
def d7723 (p : Pattern) : Int := if p 225 then d3239 p else d3250 p
theorem agree7723 (p q : Pattern) (h : Agree support p q) : d7723 p = d7723 q := by
  simp only [d7723, h 225 (by decide), agree3239 p q h, agree3250 p q h]
theorem nonnegative7723 (p : Pattern) : 0 ≤ d7723 p :=
  nonnegative_ite (p 225) (nonnegative3239 p) (nonnegative3250 p)
def d7724 (p : Pattern) : Int := if p 224 then d3239 p else d7723 p
theorem agree7724 (p q : Pattern) (h : Agree support p q) : d7724 p = d7724 q := by
  simp only [d7724, h 224 (by decide), agree3239 p q h, agree7723 p q h]
theorem nonnegative7724 (p : Pattern) : 0 ≤ d7724 p :=
  nonnegative_ite (p 224) (nonnegative3239 p) (nonnegative7723 p)
def d7725 (p : Pattern) : Int := if p 204 then d12 p else d7724 p
theorem agree7725 (p q : Pattern) (h : Agree support p q) : d7725 p = d7725 q := by
  simp only [d7725, h 204 (by decide), agree12 p q h, agree7724 p q h]
theorem nonnegative7725 (p : Pattern) : 0 ≤ d7725 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7724 p)
def d7726 (p : Pattern) : Int := if p 182 then d7725 p else d7722 p
theorem agree7726 (p q : Pattern) (h : Agree support p q) : d7726 p = d7726 q := by
  simp only [d7726, h 182 (by decide), agree7725 p q h, agree7722 p q h]
theorem nonnegative7726 (p : Pattern) : 0 ≤ d7726 p :=
  nonnegative_ite (p 182) (nonnegative7725 p) (nonnegative7722 p)
def d7727 (p : Pattern) : Int := if p 163 then d7726 p else d7668 p
theorem agree7727 (p q : Pattern) (h : Agree support p q) : d7727 p = d7727 q := by
  simp only [d7727, h 163 (by decide), agree7726 p q h, agree7668 p q h]
theorem nonnegative7727 (p : Pattern) : 0 ≤ d7727 p :=
  nonnegative_ite (p 163) (nonnegative7726 p) (nonnegative7668 p)
def d7728 (p : Pattern) : Int := if p 163 then d7684 p else d7675 p
theorem agree7728 (p q : Pattern) (h : Agree support p q) : d7728 p = d7728 q := by
  simp only [d7728, h 163 (by decide), agree7684 p q h, agree7675 p q h]
theorem nonnegative7728 (p : Pattern) : 0 ≤ d7728 p :=
  nonnegative_ite (p 163) (nonnegative7684 p) (nonnegative7675 p)
def d7729 (p : Pattern) : Int := if p 162 then d7728 p else d7727 p
theorem agree7729 (p q : Pattern) (h : Agree support p q) : d7729 p = d7729 q := by
  simp only [d7729, h 162 (by decide), agree7728 p q h, agree7727 p q h]
theorem nonnegative7729 (p : Pattern) : 0 ≤ d7729 p :=
  nonnegative_ite (p 162) (nonnegative7728 p) (nonnegative7727 p)
def d7730 (p : Pattern) : Int := if p 224 then d12 p else d7697 p
theorem agree7730 (p q : Pattern) (h : Agree support p q) : d7730 p = d7730 q := by
  simp only [d7730, h 224 (by decide), agree12 p q h, agree7697 p q h]
theorem nonnegative7730 (p : Pattern) : 0 ≤ d7730 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7697 p)
def d7731 (p : Pattern) : Int := if p 204 then d7730 p else d3279 p
theorem agree7731 (p q : Pattern) (h : Agree support p q) : d7731 p = d7731 q := by
  simp only [d7731, h 204 (by decide), agree7730 p q h, agree3279 p q h]
theorem nonnegative7731 (p : Pattern) : 0 ≤ d7731 p :=
  nonnegative_ite (p 204) (nonnegative7730 p) (nonnegative3279 p)
def d7732 (p : Pattern) : Int := if p 204 then d12 p else d7730 p
theorem agree7732 (p q : Pattern) (h : Agree support p q) : d7732 p = d7732 q := by
  simp only [d7732, h 204 (by decide), agree12 p q h, agree7730 p q h]
theorem nonnegative7732 (p : Pattern) : 0 ≤ d7732 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7730 p)
def d7733 (p : Pattern) : Int := if p 182 then d7732 p else d7731 p
theorem agree7733 (p q : Pattern) (h : Agree support p q) : d7733 p = d7733 q := by
  simp only [d7733, h 182 (by decide), agree7732 p q h, agree7731 p q h]
theorem nonnegative7733 (p : Pattern) : 0 ≤ d7733 p :=
  nonnegative_ite (p 182) (nonnegative7732 p) (nonnegative7731 p)
def d7734 (p : Pattern) : Int := if p 163 then d7733 p else d7675 p
theorem agree7734 (p q : Pattern) (h : Agree support p q) : d7734 p = d7734 q := by
  simp only [d7734, h 163 (by decide), agree7733 p q h, agree7675 p q h]
theorem nonnegative7734 (p : Pattern) : 0 ≤ d7734 p :=
  nonnegative_ite (p 163) (nonnegative7733 p) (nonnegative7675 p)
def d7735 (p : Pattern) : Int := if p 204 then d7703 p else d3257 p
theorem agree7735 (p q : Pattern) (h : Agree support p q) : d7735 p = d7735 q := by
  simp only [d7735, h 204 (by decide), agree7703 p q h, agree3257 p q h]
theorem nonnegative7735 (p : Pattern) : 0 ≤ d7735 p :=
  nonnegative_ite (p 204) (nonnegative7703 p) (nonnegative3257 p)
def d7736 (p : Pattern) : Int := if p 182 then d7704 p else d7735 p
theorem agree7736 (p q : Pattern) (h : Agree support p q) : d7736 p = d7736 q := by
  simp only [d7736, h 182 (by decide), agree7704 p q h, agree7735 p q h]
theorem nonnegative7736 (p : Pattern) : 0 ≤ d7736 p :=
  nonnegative_ite (p 182) (nonnegative7704 p) (nonnegative7735 p)
def d7737 (p : Pattern) : Int := if p 163 then d12 p else d7736 p
theorem agree7737 (p q : Pattern) (h : Agree support p q) : d7737 p = d7737 q := by
  simp only [d7737, h 163 (by decide), agree12 p q h, agree7736 p q h]
theorem nonnegative7737 (p : Pattern) : 0 ≤ d7737 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7736 p)
def d7738 (p : Pattern) : Int := if p 162 then d7737 p else d7734 p
theorem agree7738 (p q : Pattern) (h : Agree support p q) : d7738 p = d7738 q := by
  simp only [d7738, h 162 (by decide), agree7737 p q h, agree7734 p q h]
theorem nonnegative7738 (p : Pattern) : 0 ≤ d7738 p :=
  nonnegative_ite (p 162) (nonnegative7737 p) (nonnegative7734 p)
def d7739 (p : Pattern) : Int := if p 161 then d7738 p else d7729 p
theorem agree7739 (p q : Pattern) (h : Agree support p q) : d7739 p = d7739 q := by
  simp only [d7739, h 161 (by decide), agree7738 p q h, agree7729 p q h]
theorem nonnegative7739 (p : Pattern) : 0 ≤ d7739 p :=
  nonnegative_ite (p 161) (nonnegative7738 p) (nonnegative7729 p)
def d7740 (p : Pattern) : Int := if p 204 then d7694 p else d3250 p
theorem agree7740 (p q : Pattern) (h : Agree support p q) : d7740 p = d7740 q := by
  simp only [d7740, h 204 (by decide), agree7694 p q h, agree3250 p q h]
theorem nonnegative7740 (p : Pattern) : 0 ≤ d7740 p :=
  nonnegative_ite (p 204) (nonnegative7694 p) (nonnegative3250 p)
def d7741 (p : Pattern) : Int := if p 182 then d12 p else d7740 p
theorem agree7741 (p q : Pattern) (h : Agree support p q) : d7741 p = d7741 q := by
  simp only [d7741, h 182 (by decide), agree12 p q h, agree7740 p q h]
theorem nonnegative7741 (p : Pattern) : 0 ≤ d7741 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7740 p)
def d7742 (p : Pattern) : Int := if p 163 then d7741 p else d7700 p
theorem agree7742 (p q : Pattern) (h : Agree support p q) : d7742 p = d7742 q := by
  simp only [d7742, h 163 (by decide), agree7741 p q h, agree7700 p q h]
theorem nonnegative7742 (p : Pattern) : 0 ≤ d7742 p :=
  nonnegative_ite (p 163) (nonnegative7741 p) (nonnegative7700 p)
def d7743 (p : Pattern) : Int := if p 163 then d7715 p else d7710 p
theorem agree7743 (p q : Pattern) (h : Agree support p q) : d7743 p = d7743 q := by
  simp only [d7743, h 163 (by decide), agree7715 p q h, agree7710 p q h]
theorem nonnegative7743 (p : Pattern) : 0 ≤ d7743 p :=
  nonnegative_ite (p 163) (nonnegative7715 p) (nonnegative7710 p)
def d7744 (p : Pattern) : Int := if p 162 then d7743 p else d7742 p
theorem agree7744 (p q : Pattern) (h : Agree support p q) : d7744 p = d7744 q := by
  simp only [d7744, h 162 (by decide), agree7743 p q h, agree7742 p q h]
theorem nonnegative7744 (p : Pattern) : 0 ≤ d7744 p :=
  nonnegative_ite (p 162) (nonnegative7743 p) (nonnegative7742 p)
def d7745 (p : Pattern) : Int := if p 182 then d12 p else d7731 p
theorem agree7745 (p q : Pattern) (h : Agree support p q) : d7745 p = d7745 q := by
  simp only [d7745, h 182 (by decide), agree12 p q h, agree7731 p q h]
theorem nonnegative7745 (p : Pattern) : 0 ≤ d7745 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7731 p)
def d7746 (p : Pattern) : Int := if p 163 then d7745 p else d7710 p
theorem agree7746 (p q : Pattern) (h : Agree support p q) : d7746 p = d7746 q := by
  simp only [d7746, h 163 (by decide), agree7745 p q h, agree7710 p q h]
theorem nonnegative7746 (p : Pattern) : 0 ≤ d7746 p :=
  nonnegative_ite (p 163) (nonnegative7745 p) (nonnegative7710 p)
def d7747 (p : Pattern) : Int := if p 182 then d12 p else d7735 p
theorem agree7747 (p q : Pattern) (h : Agree support p q) : d7747 p = d7747 q := by
  simp only [d7747, h 182 (by decide), agree12 p q h, agree7735 p q h]
theorem nonnegative7747 (p : Pattern) : 0 ≤ d7747 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7735 p)
def d7748 (p : Pattern) : Int := if p 163 then d12 p else d7747 p
theorem agree7748 (p q : Pattern) (h : Agree support p q) : d7748 p = d7748 q := by
  simp only [d7748, h 163 (by decide), agree12 p q h, agree7747 p q h]
theorem nonnegative7748 (p : Pattern) : 0 ≤ d7748 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7747 p)
def d7749 (p : Pattern) : Int := if p 162 then d7748 p else d7746 p
theorem agree7749 (p q : Pattern) (h : Agree support p q) : d7749 p = d7749 q := by
  simp only [d7749, h 162 (by decide), agree7748 p q h, agree7746 p q h]
theorem nonnegative7749 (p : Pattern) : 0 ≤ d7749 p :=
  nonnegative_ite (p 162) (nonnegative7748 p) (nonnegative7746 p)
def d7750 (p : Pattern) : Int := if p 161 then d7749 p else d7744 p
theorem agree7750 (p q : Pattern) (h : Agree support p q) : d7750 p = d7750 q := by
  simp only [d7750, h 161 (by decide), agree7749 p q h, agree7744 p q h]
theorem nonnegative7750 (p : Pattern) : 0 ≤ d7750 p :=
  nonnegative_ite (p 161) (nonnegative7749 p) (nonnegative7744 p)
def d7751 (p : Pattern) : Int := if p 160 then d7750 p else d7739 p
theorem agree7751 (p q : Pattern) (h : Agree support p q) : d7751 p = d7751 q := by
  simp only [d7751, h 160 (by decide), agree7750 p q h, agree7739 p q h]
theorem nonnegative7751 (p : Pattern) : 0 ≤ d7751 p :=
  nonnegative_ite (p 160) (nonnegative7750 p) (nonnegative7739 p)
def d7752 (p : Pattern) : Int := if p 141 then d7751 p else d7719 p
theorem agree7752 (p q : Pattern) (h : Agree support p q) : d7752 p = d7752 q := by
  simp only [d7752, h 141 (by decide), agree7751 p q h, agree7719 p q h]
theorem nonnegative7752 (p : Pattern) : 0 ≤ d7752 p :=
  nonnegative_ite (p 141) (nonnegative7751 p) (nonnegative7719 p)
def d7753 (p : Pattern) : Int := if p 224 then d7672 p else d7688 p
theorem agree7753 (p q : Pattern) (h : Agree support p q) : d7753 p = d7753 q := by
  simp only [d7753, h 224 (by decide), agree7672 p q h, agree7688 p q h]
theorem nonnegative7753 (p : Pattern) : 0 ≤ d7753 p :=
  nonnegative_ite (p 224) (nonnegative7672 p) (nonnegative7688 p)
def d7754 (p : Pattern) : Int := if p 204 then d7753 p else d3226 p
theorem agree7754 (p q : Pattern) (h : Agree support p q) : d7754 p = d7754 q := by
  simp only [d7754, h 204 (by decide), agree7753 p q h, agree3226 p q h]
theorem nonnegative7754 (p : Pattern) : 0 ≤ d7754 p :=
  nonnegative_ite (p 204) (nonnegative7753 p) (nonnegative3226 p)
def d7755 (p : Pattern) : Int := if p 204 then d12 p else d7663 p
theorem agree7755 (p q : Pattern) (h : Agree support p q) : d7755 p = d7755 q := by
  simp only [d7755, h 204 (by decide), agree12 p q h, agree7663 p q h]
theorem nonnegative7755 (p : Pattern) : 0 ≤ d7755 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7663 p)
def d7756 (p : Pattern) : Int := if p 182 then d7755 p else d7754 p
theorem agree7756 (p q : Pattern) (h : Agree support p q) : d7756 p = d7756 q := by
  simp only [d7756, h 182 (by decide), agree7755 p q h, agree7754 p q h]
theorem nonnegative7756 (p : Pattern) : 0 ≤ d7756 p :=
  nonnegative_ite (p 182) (nonnegative7755 p) (nonnegative7754 p)
def d7757 (p : Pattern) : Int := if p 224 then d7706 p else d7688 p
theorem agree7757 (p q : Pattern) (h : Agree support p q) : d7757 p = d7757 q := by
  simp only [d7757, h 224 (by decide), agree7706 p q h, agree7688 p q h]
theorem nonnegative7757 (p : Pattern) : 0 ≤ d7757 p :=
  nonnegative_ite (p 224) (nonnegative7706 p) (nonnegative7688 p)
def d7758 (p : Pattern) : Int := if p 204 then d7757 p else d3226 p
theorem agree7758 (p q : Pattern) (h : Agree support p q) : d7758 p = d7758 q := by
  simp only [d7758, h 204 (by decide), agree7757 p q h, agree3226 p q h]
theorem nonnegative7758 (p : Pattern) : 0 ≤ d7758 p :=
  nonnegative_ite (p 204) (nonnegative7757 p) (nonnegative3226 p)
def d7759 (p : Pattern) : Int := if p 224 then d7669 p else d7688 p
theorem agree7759 (p q : Pattern) (h : Agree support p q) : d7759 p = d7759 q := by
  simp only [d7759, h 224 (by decide), agree7669 p q h, agree7688 p q h]
theorem nonnegative7759 (p : Pattern) : 0 ≤ d7759 p :=
  nonnegative_ite (p 224) (nonnegative7669 p) (nonnegative7688 p)
def d7760 (p : Pattern) : Int := if p 204 then d12 p else d7759 p
theorem agree7760 (p q : Pattern) (h : Agree support p q) : d7760 p = d7760 q := by
  simp only [d7760, h 204 (by decide), agree12 p q h, agree7759 p q h]
theorem nonnegative7760 (p : Pattern) : 0 ≤ d7760 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7759 p)
def d7761 (p : Pattern) : Int := if p 182 then d7760 p else d7758 p
theorem agree7761 (p q : Pattern) (h : Agree support p q) : d7761 p = d7761 q := by
  simp only [d7761, h 182 (by decide), agree7760 p q h, agree7758 p q h]
theorem nonnegative7761 (p : Pattern) : 0 ≤ d7761 p :=
  nonnegative_ite (p 182) (nonnegative7760 p) (nonnegative7758 p)
def d7762 (p : Pattern) : Int := if p 163 then d7761 p else d7756 p
theorem agree7762 (p q : Pattern) (h : Agree support p q) : d7762 p = d7762 q := by
  simp only [d7762, h 163 (by decide), agree7761 p q h, agree7756 p q h]
theorem nonnegative7762 (p : Pattern) : 0 ≤ d7762 p :=
  nonnegative_ite (p 163) (nonnegative7761 p) (nonnegative7756 p)
def d7763 (p : Pattern) : Int := if p 204 then d12 p else d7690 p
theorem agree7763 (p q : Pattern) (h : Agree support p q) : d7763 p = d7763 q := by
  simp only [d7763, h 204 (by decide), agree12 p q h, agree7690 p q h]
theorem nonnegative7763 (p : Pattern) : 0 ≤ d7763 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7690 p)
def d7764 (p : Pattern) : Int := if p 182 then d7763 p else d7691 p
theorem agree7764 (p q : Pattern) (h : Agree support p q) : d7764 p = d7764 q := by
  simp only [d7764, h 182 (by decide), agree7763 p q h, agree7691 p q h]
theorem nonnegative7764 (p : Pattern) : 0 ≤ d7764 p :=
  nonnegative_ite (p 182) (nonnegative7763 p) (nonnegative7691 p)
def d7765 (p : Pattern) : Int := if p 204 then d12 p else d7708 p
theorem agree7765 (p q : Pattern) (h : Agree support p q) : d7765 p = d7765 q := by
  simp only [d7765, h 204 (by decide), agree12 p q h, agree7708 p q h]
theorem nonnegative7765 (p : Pattern) : 0 ≤ d7765 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7708 p)
def d7766 (p : Pattern) : Int := if p 182 then d7765 p else d7709 p
theorem agree7766 (p q : Pattern) (h : Agree support p q) : d7766 p = d7766 q := by
  simp only [d7766, h 182 (by decide), agree7765 p q h, agree7709 p q h]
theorem nonnegative7766 (p : Pattern) : 0 ≤ d7766 p :=
  nonnegative_ite (p 182) (nonnegative7765 p) (nonnegative7709 p)
def d7767 (p : Pattern) : Int := if p 163 then d7766 p else d7764 p
theorem agree7767 (p q : Pattern) (h : Agree support p q) : d7767 p = d7767 q := by
  simp only [d7767, h 163 (by decide), agree7766 p q h, agree7764 p q h]
theorem nonnegative7767 (p : Pattern) : 0 ≤ d7767 p :=
  nonnegative_ite (p 163) (nonnegative7766 p) (nonnegative7764 p)
def d7768 (p : Pattern) : Int := if p 162 then d7767 p else d7762 p
theorem agree7768 (p q : Pattern) (h : Agree support p q) : d7768 p = d7768 q := by
  simp only [d7768, h 162 (by decide), agree7767 p q h, agree7762 p q h]
theorem nonnegative7768 (p : Pattern) : 0 ≤ d7768 p :=
  nonnegative_ite (p 162) (nonnegative7767 p) (nonnegative7762 p)
def d7769 (p : Pattern) : Int := if p 204 then d12 p else d7679 p
theorem agree7769 (p q : Pattern) (h : Agree support p q) : d7769 p = d7769 q := by
  simp only [d7769, h 204 (by decide), agree12 p q h, agree7679 p q h]
theorem nonnegative7769 (p : Pattern) : 0 ≤ d7769 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7679 p)
def d7770 (p : Pattern) : Int := if p 182 then d7769 p else d7680 p
theorem agree7770 (p q : Pattern) (h : Agree support p q) : d7770 p = d7770 q := by
  simp only [d7770, h 182 (by decide), agree7769 p q h, agree7680 p q h]
theorem nonnegative7770 (p : Pattern) : 0 ≤ d7770 p :=
  nonnegative_ite (p 182) (nonnegative7769 p) (nonnegative7680 p)
def d7771 (p : Pattern) : Int := if p 163 then d12 p else d7770 p
theorem agree7771 (p q : Pattern) (h : Agree support p q) : d7771 p = d7771 q := by
  simp only [d7771, h 163 (by decide), agree12 p q h, agree7770 p q h]
theorem nonnegative7771 (p : Pattern) : 0 ≤ d7771 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7770 p)
def d7772 (p : Pattern) : Int := if p 162 then d7771 p else d7767 p
theorem agree7772 (p q : Pattern) (h : Agree support p q) : d7772 p = d7772 q := by
  simp only [d7772, h 162 (by decide), agree7771 p q h, agree7767 p q h]
theorem nonnegative7772 (p : Pattern) : 0 ≤ d7772 p :=
  nonnegative_ite (p 162) (nonnegative7771 p) (nonnegative7767 p)
def d7773 (p : Pattern) : Int := if p 161 then d7772 p else d7768 p
theorem agree7773 (p q : Pattern) (h : Agree support p q) : d7773 p = d7773 q := by
  simp only [d7773, h 161 (by decide), agree7772 p q h, agree7768 p q h]
theorem nonnegative7773 (p : Pattern) : 0 ≤ d7773 p :=
  nonnegative_ite (p 161) (nonnegative7772 p) (nonnegative7768 p)
def d7774 (p : Pattern) : Int := if p 182 then d7695 p else d7740 p
theorem agree7774 (p q : Pattern) (h : Agree support p q) : d7774 p = d7774 q := by
  simp only [d7774, h 182 (by decide), agree7695 p q h, agree7740 p q h]
theorem nonnegative7774 (p : Pattern) : 0 ≤ d7774 p :=
  nonnegative_ite (p 182) (nonnegative7695 p) (nonnegative7740 p)
def d7775 (p : Pattern) : Int := if p 204 then d7698 p else d3253 p
theorem agree7775 (p q : Pattern) (h : Agree support p q) : d7775 p = d7775 q := by
  simp only [d7775, h 204 (by decide), agree7698 p q h, agree3253 p q h]
theorem nonnegative7775 (p : Pattern) : 0 ≤ d7775 p :=
  nonnegative_ite (p 204) (nonnegative7698 p) (nonnegative3253 p)
def d7776 (p : Pattern) : Int := if p 182 then d7699 p else d7775 p
theorem agree7776 (p q : Pattern) (h : Agree support p q) : d7776 p = d7776 q := by
  simp only [d7776, h 182 (by decide), agree7699 p q h, agree7775 p q h]
theorem nonnegative7776 (p : Pattern) : 0 ≤ d7776 p :=
  nonnegative_ite (p 182) (nonnegative7699 p) (nonnegative7775 p)
def d7777 (p : Pattern) : Int := if p 163 then d7776 p else d7774 p
theorem agree7777 (p q : Pattern) (h : Agree support p q) : d7777 p = d7777 q := by
  simp only [d7777, h 163 (by decide), agree7776 p q h, agree7774 p q h]
theorem nonnegative7777 (p : Pattern) : 0 ≤ d7777 p :=
  nonnegative_ite (p 163) (nonnegative7776 p) (nonnegative7774 p)
def d7778 (p : Pattern) : Int := if p 162 then d7737 p else d7777 p
theorem agree7778 (p q : Pattern) (h : Agree support p q) : d7778 p = d7778 q := by
  simp only [d7778, h 162 (by decide), agree7737 p q h, agree7777 p q h]
theorem nonnegative7778 (p : Pattern) : 0 ≤ d7778 p :=
  nonnegative_ite (p 162) (nonnegative7737 p) (nonnegative7777 p)
def d7779 (p : Pattern) : Int := if p 161 then d12 p else d7778 p
theorem agree7779 (p q : Pattern) (h : Agree support p q) : d7779 p = d7779 q := by
  simp only [d7779, h 161 (by decide), agree12 p q h, agree7778 p q h]
theorem nonnegative7779 (p : Pattern) : 0 ≤ d7779 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7778 p)
def d7780 (p : Pattern) : Int := if p 160 then d7779 p else d7773 p
theorem agree7780 (p q : Pattern) (h : Agree support p q) : d7780 p = d7780 q := by
  simp only [d7780, h 160 (by decide), agree7779 p q h, agree7773 p q h]
theorem nonnegative7780 (p : Pattern) : 0 ≤ d7780 p :=
  nonnegative_ite (p 160) (nonnegative7779 p) (nonnegative7773 p)
def d7781 (p : Pattern) : Int := if p 163 then d7774 p else d7761 p
theorem agree7781 (p q : Pattern) (h : Agree support p q) : d7781 p = d7781 q := by
  simp only [d7781, h 163 (by decide), agree7774 p q h, agree7761 p q h]
theorem nonnegative7781 (p : Pattern) : 0 ≤ d7781 p :=
  nonnegative_ite (p 163) (nonnegative7774 p) (nonnegative7761 p)
def d7782 (p : Pattern) : Int := if p 163 then d7770 p else d7766 p
theorem agree7782 (p q : Pattern) (h : Agree support p q) : d7782 p = d7782 q := by
  simp only [d7782, h 163 (by decide), agree7770 p q h, agree7766 p q h]
theorem nonnegative7782 (p : Pattern) : 0 ≤ d7782 p :=
  nonnegative_ite (p 163) (nonnegative7770 p) (nonnegative7766 p)
def d7783 (p : Pattern) : Int := if p 162 then d7782 p else d7781 p
theorem agree7783 (p q : Pattern) (h : Agree support p q) : d7783 p = d7783 q := by
  simp only [d7783, h 162 (by decide), agree7782 p q h, agree7781 p q h]
theorem nonnegative7783 (p : Pattern) : 0 ≤ d7783 p :=
  nonnegative_ite (p 162) (nonnegative7782 p) (nonnegative7781 p)
def d7784 (p : Pattern) : Int := if p 163 then d7733 p else d7766 p
theorem agree7784 (p q : Pattern) (h : Agree support p q) : d7784 p = d7784 q := by
  simp only [d7784, h 163 (by decide), agree7733 p q h, agree7766 p q h]
theorem nonnegative7784 (p : Pattern) : 0 ≤ d7784 p :=
  nonnegative_ite (p 163) (nonnegative7733 p) (nonnegative7766 p)
def d7785 (p : Pattern) : Int := if p 162 then d7737 p else d7784 p
theorem agree7785 (p q : Pattern) (h : Agree support p q) : d7785 p = d7785 q := by
  simp only [d7785, h 162 (by decide), agree7737 p q h, agree7784 p q h]
theorem nonnegative7785 (p : Pattern) : 0 ≤ d7785 p :=
  nonnegative_ite (p 162) (nonnegative7737 p) (nonnegative7784 p)
def d7786 (p : Pattern) : Int := if p 161 then d7785 p else d7783 p
theorem agree7786 (p q : Pattern) (h : Agree support p q) : d7786 p = d7786 q := by
  simp only [d7786, h 161 (by decide), agree7785 p q h, agree7783 p q h]
theorem nonnegative7786 (p : Pattern) : 0 ≤ d7786 p :=
  nonnegative_ite (p 161) (nonnegative7785 p) (nonnegative7783 p)
def d7787 (p : Pattern) : Int := if p 163 then d12 p else d7776 p
theorem agree7787 (p q : Pattern) (h : Agree support p q) : d7787 p = d7787 q := by
  simp only [d7787, h 163 (by decide), agree12 p q h, agree7776 p q h]
theorem nonnegative7787 (p : Pattern) : 0 ≤ d7787 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7776 p)
def d7788 (p : Pattern) : Int := if p 162 then d12 p else d7787 p
theorem agree7788 (p q : Pattern) (h : Agree support p q) : d7788 p = d7788 q := by
  simp only [d7788, h 162 (by decide), agree12 p q h, agree7787 p q h]
theorem nonnegative7788 (p : Pattern) : 0 ≤ d7788 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7787 p)
def d7789 (p : Pattern) : Int := if p 161 then d12 p else d7788 p
theorem agree7789 (p q : Pattern) (h : Agree support p q) : d7789 p = d7789 q := by
  simp only [d7789, h 161 (by decide), agree12 p q h, agree7788 p q h]
theorem nonnegative7789 (p : Pattern) : 0 ≤ d7789 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7788 p)
def d7790 (p : Pattern) : Int := if p 160 then d7789 p else d7786 p
theorem agree7790 (p q : Pattern) (h : Agree support p q) : d7790 p = d7790 q := by
  simp only [d7790, h 160 (by decide), agree7789 p q h, agree7786 p q h]
theorem nonnegative7790 (p : Pattern) : 0 ≤ d7790 p :=
  nonnegative_ite (p 160) (nonnegative7789 p) (nonnegative7786 p)
def d7791 (p : Pattern) : Int := if p 141 then d7790 p else d7780 p
theorem agree7791 (p q : Pattern) (h : Agree support p q) : d7791 p = d7791 q := by
  simp only [d7791, h 141 (by decide), agree7790 p q h, agree7780 p q h]
theorem nonnegative7791 (p : Pattern) : 0 ≤ d7791 p :=
  nonnegative_ite (p 141) (nonnegative7790 p) (nonnegative7780 p)
def d7792 (p : Pattern) : Int := if p 138 then d7791 p else d7752 p
theorem agree7792 (p q : Pattern) (h : Agree support p q) : d7792 p = d7792 q := by
  simp only [d7792, h 138 (by decide), agree7791 p q h, agree7752 p q h]
theorem nonnegative7792 (p : Pattern) : 0 ≤ d7792 p :=
  nonnegative_ite (p 138) (nonnegative7791 p) (nonnegative7752 p)
def d7793 (p : Pattern) : Int := if p 163 then d7736 p else d7770 p
theorem agree7793 (p q : Pattern) (h : Agree support p q) : d7793 p = d7793 q := by
  simp only [d7793, h 163 (by decide), agree7736 p q h, agree7770 p q h]
theorem nonnegative7793 (p : Pattern) : 0 ≤ d7793 p :=
  nonnegative_ite (p 163) (nonnegative7736 p) (nonnegative7770 p)
def d7794 (p : Pattern) : Int := if p 162 then d7737 p else d7793 p
theorem agree7794 (p q : Pattern) (h : Agree support p q) : d7794 p = d7794 q := by
  simp only [d7794, h 162 (by decide), agree7737 p q h, agree7793 p q h]
theorem nonnegative7794 (p : Pattern) : 0 ≤ d7794 p :=
  nonnegative_ite (p 162) (nonnegative7737 p) (nonnegative7793 p)
def d7795 (p : Pattern) : Int := if p 162 then d12 p else d7737 p
theorem agree7795 (p q : Pattern) (h : Agree support p q) : d7795 p = d7795 q := by
  simp only [d7795, h 162 (by decide), agree12 p q h, agree7737 p q h]
theorem nonnegative7795 (p : Pattern) : 0 ≤ d7795 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7737 p)
def d7796 (p : Pattern) : Int := if p 161 then d7795 p else d7794 p
theorem agree7796 (p q : Pattern) (h : Agree support p q) : d7796 p = d7796 q := by
  simp only [d7796, h 161 (by decide), agree7795 p q h, agree7794 p q h]
theorem nonnegative7796 (p : Pattern) : 0 ≤ d7796 p :=
  nonnegative_ite (p 161) (nonnegative7795 p) (nonnegative7794 p)
def d7797 (p : Pattern) : Int := if p 161 then d12 p else d7795 p
theorem agree7797 (p q : Pattern) (h : Agree support p q) : d7797 p = d7797 q := by
  simp only [d7797, h 161 (by decide), agree12 p q h, agree7795 p q h]
theorem nonnegative7797 (p : Pattern) : 0 ≤ d7797 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7795 p)
def d7798 (p : Pattern) : Int := if p 160 then d7797 p else d7796 p
theorem agree7798 (p q : Pattern) (h : Agree support p q) : d7798 p = d7798 q := by
  simp only [d7798, h 160 (by decide), agree7797 p q h, agree7796 p q h]
theorem nonnegative7798 (p : Pattern) : 0 ≤ d7798 p :=
  nonnegative_ite (p 160) (nonnegative7797 p) (nonnegative7796 p)
def d7799 (p : Pattern) : Int := if p 160 then d12 p else d7797 p
theorem agree7799 (p q : Pattern) (h : Agree support p q) : d7799 p = d7799 q := by
  simp only [d7799, h 160 (by decide), agree12 p q h, agree7797 p q h]
theorem nonnegative7799 (p : Pattern) : 0 ≤ d7799 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative7797 p)
end NetHack.Sokoban22Refined85
