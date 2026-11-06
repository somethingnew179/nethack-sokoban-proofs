/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7800 (p : Pattern) : Int := if p 141 then d7799 p else d7798 p
theorem agree7800 (p q : Pattern) (h : Agree support p q) : d7800 p = d7800 q := by
  simp only [d7800, h 141 (by decide), agree7799 p q h, agree7798 p q h]
theorem nonnegative7800 (p : Pattern) : 0 ≤ d7800 p :=
  nonnegative_ite (p 141) (nonnegative7799 p) (nonnegative7798 p)
def d7801 (p : Pattern) : Int := if p 138 then d7800 p else d7791 p
theorem agree7801 (p q : Pattern) (h : Agree support p q) : d7801 p = d7801 q := by
  simp only [d7801, h 138 (by decide), agree7800 p q h, agree7791 p q h]
theorem nonnegative7801 (p : Pattern) : 0 ≤ d7801 p :=
  nonnegative_ite (p 138) (nonnegative7800 p) (nonnegative7791 p)
def d7802 (p : Pattern) : Int := if p 116 then d7801 p else d7792 p
theorem agree7802 (p q : Pattern) (h : Agree support p q) : d7802 p = d7802 q := by
  simp only [d7802, h 116 (by decide), agree7801 p q h, agree7792 p q h]
theorem nonnegative7802 (p : Pattern) : 0 ≤ d7802 p :=
  nonnegative_ite (p 116) (nonnegative7801 p) (nonnegative7792 p)
def d7803 (p : Pattern) : Int := if p 138 then d12 p else d7791 p
theorem agree7803 (p q : Pattern) (h : Agree support p q) : d7803 p = d7803 q := by
  simp only [d7803, h 138 (by decide), agree12 p q h, agree7791 p q h]
theorem nonnegative7803 (p : Pattern) : 0 ≤ d7803 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7791 p)
def d7804 (p : Pattern) : Int := if p 116 then d7803 p else d7792 p
theorem agree7804 (p q : Pattern) (h : Agree support p q) : d7804 p = d7804 q := by
  simp only [d7804, h 116 (by decide), agree7803 p q h, agree7792 p q h]
theorem nonnegative7804 (p : Pattern) : 0 ≤ d7804 p :=
  nonnegative_ite (p 116) (nonnegative7803 p) (nonnegative7792 p)
def d7805 (p : Pattern) : Int := if p 115 then d7804 p else d7802 p
theorem agree7805 (p q : Pattern) (h : Agree support p q) : d7805 p = d7805 q := by
  simp only [d7805, h 115 (by decide), agree7804 p q h, agree7802 p q h]
theorem nonnegative7805 (p : Pattern) : 0 ≤ d7805 p :=
  nonnegative_ite (p 115) (nonnegative7804 p) (nonnegative7802 p)
def d7806 (p : Pattern) : Int := if p 225 then d3366 p else d3358 p
theorem agree7806 (p q : Pattern) (h : Agree support p q) : d7806 p = d7806 q := by
  simp only [d7806, h 225 (by decide), agree3366 p q h, agree3358 p q h]
theorem nonnegative7806 (p : Pattern) : 0 ≤ d7806 p :=
  nonnegative_ite (p 225) (nonnegative3366 p) (nonnegative3358 p)
def d7807 (p : Pattern) : Int := if p 224 then d3366 p else d7806 p
theorem agree7807 (p q : Pattern) (h : Agree support p q) : d7807 p = d7807 q := by
  simp only [d7807, h 224 (by decide), agree3366 p q h, agree7806 p q h]
theorem nonnegative7807 (p : Pattern) : 0 ≤ d7807 p :=
  nonnegative_ite (p 224) (nonnegative3366 p) (nonnegative7806 p)
def d7808 (p : Pattern) : Int := if p 204 then d7807 p else d3358 p
theorem agree7808 (p q : Pattern) (h : Agree support p q) : d7808 p = d7808 q := by
  simp only [d7808, h 204 (by decide), agree7807 p q h, agree3358 p q h]
theorem nonnegative7808 (p : Pattern) : 0 ≤ d7808 p :=
  nonnegative_ite (p 204) (nonnegative7807 p) (nonnegative3358 p)
def d7809 (p : Pattern) : Int := if p 225 then d3374 p else d3358 p
theorem agree7809 (p q : Pattern) (h : Agree support p q) : d7809 p = d7809 q := by
  simp only [d7809, h 225 (by decide), agree3374 p q h, agree3358 p q h]
theorem nonnegative7809 (p : Pattern) : 0 ≤ d7809 p :=
  nonnegative_ite (p 225) (nonnegative3374 p) (nonnegative3358 p)
def d7810 (p : Pattern) : Int := if p 224 then d3374 p else d7809 p
theorem agree7810 (p q : Pattern) (h : Agree support p q) : d7810 p = d7810 q := by
  simp only [d7810, h 224 (by decide), agree3374 p q h, agree7809 p q h]
theorem nonnegative7810 (p : Pattern) : 0 ≤ d7810 p :=
  nonnegative_ite (p 224) (nonnegative3374 p) (nonnegative7809 p)
def d7811 (p : Pattern) : Int := if p 204 then d12 p else d7810 p
theorem agree7811 (p q : Pattern) (h : Agree support p q) : d7811 p = d7811 q := by
  simp only [d7811, h 204 (by decide), agree12 p q h, agree7810 p q h]
theorem nonnegative7811 (p : Pattern) : 0 ≤ d7811 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7810 p)
def d7812 (p : Pattern) : Int := if p 182 then d7811 p else d7808 p
theorem agree7812 (p q : Pattern) (h : Agree support p q) : d7812 p = d7812 q := by
  simp only [d7812, h 182 (by decide), agree7811 p q h, agree7808 p q h]
theorem nonnegative7812 (p : Pattern) : 0 ≤ d7812 p :=
  nonnegative_ite (p 182) (nonnegative7811 p) (nonnegative7808 p)
def d7813 (p : Pattern) : Int := if p 225 then d3244 p else d3366 p
theorem agree7813 (p q : Pattern) (h : Agree support p q) : d7813 p = d7813 q := by
  simp only [d7813, h 225 (by decide), agree3244 p q h, agree3366 p q h]
theorem nonnegative7813 (p : Pattern) : 0 ≤ d7813 p :=
  nonnegative_ite (p 225) (nonnegative3244 p) (nonnegative3366 p)
def d7814 (p : Pattern) : Int := if p 224 then d3244 p else d7813 p
theorem agree7814 (p q : Pattern) (h : Agree support p q) : d7814 p = d7814 q := by
  simp only [d7814, h 224 (by decide), agree3244 p q h, agree7813 p q h]
theorem nonnegative7814 (p : Pattern) : 0 ≤ d7814 p :=
  nonnegative_ite (p 224) (nonnegative3244 p) (nonnegative7813 p)
def d7815 (p : Pattern) : Int := if p 204 then d7814 p else d3366 p
theorem agree7815 (p q : Pattern) (h : Agree support p q) : d7815 p = d7815 q := by
  simp only [d7815, h 204 (by decide), agree7814 p q h, agree3366 p q h]
theorem nonnegative7815 (p : Pattern) : 0 ≤ d7815 p :=
  nonnegative_ite (p 204) (nonnegative7814 p) (nonnegative3366 p)
def d7816 (p : Pattern) : Int := if p 225 then d3377 p else d3366 p
theorem agree7816 (p q : Pattern) (h : Agree support p q) : d7816 p = d7816 q := by
  simp only [d7816, h 225 (by decide), agree3377 p q h, agree3366 p q h]
theorem nonnegative7816 (p : Pattern) : 0 ≤ d7816 p :=
  nonnegative_ite (p 225) (nonnegative3377 p) (nonnegative3366 p)
def d7817 (p : Pattern) : Int := if p 224 then d3377 p else d7816 p
theorem agree7817 (p q : Pattern) (h : Agree support p q) : d7817 p = d7817 q := by
  simp only [d7817, h 224 (by decide), agree3377 p q h, agree7816 p q h]
theorem nonnegative7817 (p : Pattern) : 0 ≤ d7817 p :=
  nonnegative_ite (p 224) (nonnegative3377 p) (nonnegative7816 p)
def d7818 (p : Pattern) : Int := if p 204 then d12 p else d7817 p
theorem agree7818 (p q : Pattern) (h : Agree support p q) : d7818 p = d7818 q := by
  simp only [d7818, h 204 (by decide), agree12 p q h, agree7817 p q h]
theorem nonnegative7818 (p : Pattern) : 0 ≤ d7818 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7817 p)
def d7819 (p : Pattern) : Int := if p 182 then d7818 p else d7815 p
theorem agree7819 (p q : Pattern) (h : Agree support p q) : d7819 p = d7819 q := by
  simp only [d7819, h 182 (by decide), agree7818 p q h, agree7815 p q h]
theorem nonnegative7819 (p : Pattern) : 0 ≤ d7819 p :=
  nonnegative_ite (p 182) (nonnegative7818 p) (nonnegative7815 p)
def d7820 (p : Pattern) : Int := if p 163 then d7819 p else d7812 p
theorem agree7820 (p q : Pattern) (h : Agree support p q) : d7820 p = d7820 q := by
  simp only [d7820, h 163 (by decide), agree7819 p q h, agree7812 p q h]
theorem nonnegative7820 (p : Pattern) : 0 ≤ d7820 p :=
  nonnegative_ite (p 163) (nonnegative7819 p) (nonnegative7812 p)
def d7821 (p : Pattern) : Int := if p 162 then d7820 p else d7812 p
theorem agree7821 (p q : Pattern) (h : Agree support p q) : d7821 p = d7821 q := by
  simp only [d7821, h 162 (by decide), agree7820 p q h, agree7812 p q h]
theorem nonnegative7821 (p : Pattern) : 0 ≤ d7821 p :=
  nonnegative_ite (p 162) (nonnegative7820 p) (nonnegative7812 p)
def d7822 (p : Pattern) : Int := if p 163 then d12 p else d7733 p
theorem agree7822 (p q : Pattern) (h : Agree support p q) : d7822 p = d7822 q := by
  simp only [d7822, h 163 (by decide), agree12 p q h, agree7733 p q h]
theorem nonnegative7822 (p : Pattern) : 0 ≤ d7822 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7733 p)
def d7823 (p : Pattern) : Int := if p 162 then d7822 p else d7820 p
theorem agree7823 (p q : Pattern) (h : Agree support p q) : d7823 p = d7823 q := by
  simp only [d7823, h 162 (by decide), agree7822 p q h, agree7820 p q h]
theorem nonnegative7823 (p : Pattern) : 0 ≤ d7823 p :=
  nonnegative_ite (p 162) (nonnegative7822 p) (nonnegative7820 p)
def d7824 (p : Pattern) : Int := if p 161 then d7823 p else d7821 p
theorem agree7824 (p q : Pattern) (h : Agree support p q) : d7824 p = d7824 q := by
  simp only [d7824, h 161 (by decide), agree7823 p q h, agree7821 p q h]
theorem nonnegative7824 (p : Pattern) : 0 ≤ d7824 p :=
  nonnegative_ite (p 161) (nonnegative7823 p) (nonnegative7821 p)
def d7825 (p : Pattern) : Int := if p 225 then d3377 p else d3358 p
theorem agree7825 (p q : Pattern) (h : Agree support p q) : d7825 p = d7825 q := by
  simp only [d7825, h 225 (by decide), agree3377 p q h, agree3358 p q h]
theorem nonnegative7825 (p : Pattern) : 0 ≤ d7825 p :=
  nonnegative_ite (p 225) (nonnegative3377 p) (nonnegative3358 p)
def d7826 (p : Pattern) : Int := if p 225 then d12 p else d3366 p
theorem agree7826 (p q : Pattern) (h : Agree support p q) : d7826 p = d7826 q := by
  simp only [d7826, h 225 (by decide), agree12 p q h, agree3366 p q h]
theorem nonnegative7826 (p : Pattern) : 0 ≤ d7826 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative3366 p)
def d7827 (p : Pattern) : Int := if p 224 then d7826 p else d7825 p
theorem agree7827 (p q : Pattern) (h : Agree support p q) : d7827 p = d7827 q := by
  simp only [d7827, h 224 (by decide), agree7826 p q h, agree7825 p q h]
theorem nonnegative7827 (p : Pattern) : 0 ≤ d7827 p :=
  nonnegative_ite (p 224) (nonnegative7826 p) (nonnegative7825 p)
def d7828 (p : Pattern) : Int := if p 204 then d7827 p else d3358 p
theorem agree7828 (p q : Pattern) (h : Agree support p q) : d7828 p = d7828 q := by
  simp only [d7828, h 204 (by decide), agree7827 p q h, agree3358 p q h]
theorem nonnegative7828 (p : Pattern) : 0 ≤ d7828 p :=
  nonnegative_ite (p 204) (nonnegative7827 p) (nonnegative3358 p)
def d7829 (p : Pattern) : Int := if p 225 then d3244 p else d3374 p
theorem agree7829 (p q : Pattern) (h : Agree support p q) : d7829 p = d7829 q := by
  simp only [d7829, h 225 (by decide), agree3244 p q h, agree3374 p q h]
theorem nonnegative7829 (p : Pattern) : 0 ≤ d7829 p :=
  nonnegative_ite (p 225) (nonnegative3244 p) (nonnegative3374 p)
def d7830 (p : Pattern) : Int := if p 225 then d12 p else d3377 p
theorem agree7830 (p q : Pattern) (h : Agree support p q) : d7830 p = d7830 q := by
  simp only [d7830, h 225 (by decide), agree12 p q h, agree3377 p q h]
theorem nonnegative7830 (p : Pattern) : 0 ≤ d7830 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative3377 p)
def d7831 (p : Pattern) : Int := if p 224 then d7830 p else d7829 p
theorem agree7831 (p q : Pattern) (h : Agree support p q) : d7831 p = d7831 q := by
  simp only [d7831, h 224 (by decide), agree7830 p q h, agree7829 p q h]
theorem nonnegative7831 (p : Pattern) : 0 ≤ d7831 p :=
  nonnegative_ite (p 224) (nonnegative7830 p) (nonnegative7829 p)
def d7832 (p : Pattern) : Int := if p 204 then d12 p else d7831 p
theorem agree7832 (p q : Pattern) (h : Agree support p q) : d7832 p = d7832 q := by
  simp only [d7832, h 204 (by decide), agree12 p q h, agree7831 p q h]
theorem nonnegative7832 (p : Pattern) : 0 ≤ d7832 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7831 p)
def d7833 (p : Pattern) : Int := if p 182 then d7832 p else d7828 p
theorem agree7833 (p q : Pattern) (h : Agree support p q) : d7833 p = d7833 q := by
  simp only [d7833, h 182 (by decide), agree7832 p q h, agree7828 p q h]
theorem nonnegative7833 (p : Pattern) : 0 ≤ d7833 p :=
  nonnegative_ite (p 182) (nonnegative7832 p) (nonnegative7828 p)
def d7834 (p : Pattern) : Int := if p 224 then d7702 p else d7830 p
theorem agree7834 (p q : Pattern) (h : Agree support p q) : d7834 p = d7834 q := by
  simp only [d7834, h 224 (by decide), agree7702 p q h, agree7830 p q h]
theorem nonnegative7834 (p : Pattern) : 0 ≤ d7834 p :=
  nonnegative_ite (p 224) (nonnegative7702 p) (nonnegative7830 p)
def d7835 (p : Pattern) : Int := if p 204 then d12 p else d7834 p
theorem agree7835 (p q : Pattern) (h : Agree support p q) : d7835 p = d7835 q := by
  simp only [d7835, h 204 (by decide), agree12 p q h, agree7834 p q h]
theorem nonnegative7835 (p : Pattern) : 0 ≤ d7835 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7834 p)
def d7836 (p : Pattern) : Int := if p 182 then d7835 p else d7828 p
theorem agree7836 (p q : Pattern) (h : Agree support p q) : d7836 p = d7836 q := by
  simp only [d7836, h 182 (by decide), agree7835 p q h, agree7828 p q h]
theorem nonnegative7836 (p : Pattern) : 0 ≤ d7836 p :=
  nonnegative_ite (p 182) (nonnegative7835 p) (nonnegative7828 p)
def d7837 (p : Pattern) : Int := if p 163 then d7836 p else d7833 p
theorem agree7837 (p q : Pattern) (h : Agree support p q) : d7837 p = d7837 q := by
  simp only [d7837, h 163 (by decide), agree7836 p q h, agree7833 p q h]
theorem nonnegative7837 (p : Pattern) : 0 ≤ d7837 p :=
  nonnegative_ite (p 163) (nonnegative7836 p) (nonnegative7833 p)
def d7838 (p : Pattern) : Int := if p 182 then d12 p else d7828 p
theorem agree7838 (p q : Pattern) (h : Agree support p q) : d7838 p = d7838 q := by
  simp only [d7838, h 182 (by decide), agree12 p q h, agree7828 p q h]
theorem nonnegative7838 (p : Pattern) : 0 ≤ d7838 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7828 p)
def d7839 (p : Pattern) : Int := if p 225 then d3257 p else d3366 p
theorem agree7839 (p q : Pattern) (h : Agree support p q) : d7839 p = d7839 q := by
  simp only [d7839, h 225 (by decide), agree3257 p q h, agree3366 p q h]
theorem nonnegative7839 (p : Pattern) : 0 ≤ d7839 p :=
  nonnegative_ite (p 225) (nonnegative3257 p) (nonnegative3366 p)
def d7840 (p : Pattern) : Int := if p 224 then d7678 p else d7839 p
theorem agree7840 (p q : Pattern) (h : Agree support p q) : d7840 p = d7840 q := by
  simp only [d7840, h 224 (by decide), agree7678 p q h, agree7839 p q h]
theorem nonnegative7840 (p : Pattern) : 0 ≤ d7840 p :=
  nonnegative_ite (p 224) (nonnegative7678 p) (nonnegative7839 p)
def d7841 (p : Pattern) : Int := if p 204 then d7840 p else d3366 p
theorem agree7841 (p q : Pattern) (h : Agree support p q) : d7841 p = d7841 q := by
  simp only [d7841, h 204 (by decide), agree7840 p q h, agree3366 p q h]
theorem nonnegative7841 (p : Pattern) : 0 ≤ d7841 p :=
  nonnegative_ite (p 204) (nonnegative7840 p) (nonnegative3366 p)
def d7842 (p : Pattern) : Int := if p 182 then d12 p else d7841 p
theorem agree7842 (p q : Pattern) (h : Agree support p q) : d7842 p = d7842 q := by
  simp only [d7842, h 182 (by decide), agree12 p q h, agree7841 p q h]
theorem nonnegative7842 (p : Pattern) : 0 ≤ d7842 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7841 p)
def d7843 (p : Pattern) : Int := if p 163 then d7842 p else d7838 p
theorem agree7843 (p q : Pattern) (h : Agree support p q) : d7843 p = d7843 q := by
  simp only [d7843, h 163 (by decide), agree7842 p q h, agree7838 p q h]
theorem nonnegative7843 (p : Pattern) : 0 ≤ d7843 p :=
  nonnegative_ite (p 163) (nonnegative7842 p) (nonnegative7838 p)
def d7844 (p : Pattern) : Int := if p 162 then d7843 p else d7837 p
theorem agree7844 (p q : Pattern) (h : Agree support p q) : d7844 p = d7844 q := by
  simp only [d7844, h 162 (by decide), agree7843 p q h, agree7837 p q h]
theorem nonnegative7844 (p : Pattern) : 0 ≤ d7844 p :=
  nonnegative_ite (p 162) (nonnegative7843 p) (nonnegative7837 p)
def d7845 (p : Pattern) : Int := if p 163 then d12 p else d7745 p
theorem agree7845 (p q : Pattern) (h : Agree support p q) : d7845 p = d7845 q := by
  simp only [d7845, h 163 (by decide), agree12 p q h, agree7745 p q h]
theorem nonnegative7845 (p : Pattern) : 0 ≤ d7845 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7745 p)
def d7846 (p : Pattern) : Int := if p 162 then d7845 p else d7843 p
theorem agree7846 (p q : Pattern) (h : Agree support p q) : d7846 p = d7846 q := by
  simp only [d7846, h 162 (by decide), agree7845 p q h, agree7843 p q h]
theorem nonnegative7846 (p : Pattern) : 0 ≤ d7846 p :=
  nonnegative_ite (p 162) (nonnegative7845 p) (nonnegative7843 p)
def d7847 (p : Pattern) : Int := if p 161 then d7846 p else d7844 p
theorem agree7847 (p q : Pattern) (h : Agree support p q) : d7847 p = d7847 q := by
  simp only [d7847, h 161 (by decide), agree7846 p q h, agree7844 p q h]
theorem nonnegative7847 (p : Pattern) : 0 ≤ d7847 p :=
  nonnegative_ite (p 161) (nonnegative7846 p) (nonnegative7844 p)
def d7848 (p : Pattern) : Int := if p 160 then d7847 p else d7824 p
theorem agree7848 (p q : Pattern) (h : Agree support p q) : d7848 p = d7848 q := by
  simp only [d7848, h 160 (by decide), agree7847 p q h, agree7824 p q h]
theorem nonnegative7848 (p : Pattern) : 0 ≤ d7848 p :=
  nonnegative_ite (p 160) (nonnegative7847 p) (nonnegative7824 p)
def d7849 (p : Pattern) : Int := if p 225 then d3377 p else d3374 p
theorem agree7849 (p q : Pattern) (h : Agree support p q) : d7849 p = d7849 q := by
  simp only [d7849, h 225 (by decide), agree3377 p q h, agree3374 p q h]
theorem nonnegative7849 (p : Pattern) : 0 ≤ d7849 p :=
  nonnegative_ite (p 225) (nonnegative3377 p) (nonnegative3374 p)
def d7850 (p : Pattern) : Int := if p 224 then d3377 p else d7849 p
theorem agree7850 (p q : Pattern) (h : Agree support p q) : d7850 p = d7850 q := by
  simp only [d7850, h 224 (by decide), agree3377 p q h, agree7849 p q h]
theorem nonnegative7850 (p : Pattern) : 0 ≤ d7850 p :=
  nonnegative_ite (p 224) (nonnegative3377 p) (nonnegative7849 p)
def d7851 (p : Pattern) : Int := if p 204 then d7850 p else d3374 p
theorem agree7851 (p q : Pattern) (h : Agree support p q) : d7851 p = d7851 q := by
  simp only [d7851, h 204 (by decide), agree7850 p q h, agree3374 p q h]
theorem nonnegative7851 (p : Pattern) : 0 ≤ d7851 p :=
  nonnegative_ite (p 204) (nonnegative7850 p) (nonnegative3374 p)
def d7852 (p : Pattern) : Int := if p 225 then d3366 p else d3374 p
theorem agree7852 (p q : Pattern) (h : Agree support p q) : d7852 p = d7852 q := by
  simp only [d7852, h 225 (by decide), agree3366 p q h, agree3374 p q h]
theorem nonnegative7852 (p : Pattern) : 0 ≤ d7852 p :=
  nonnegative_ite (p 225) (nonnegative3366 p) (nonnegative3374 p)
def d7853 (p : Pattern) : Int := if p 224 then d3366 p else d7852 p
theorem agree7853 (p q : Pattern) (h : Agree support p q) : d7853 p = d7853 q := by
  simp only [d7853, h 224 (by decide), agree3366 p q h, agree7852 p q h]
theorem nonnegative7853 (p : Pattern) : 0 ≤ d7853 p :=
  nonnegative_ite (p 224) (nonnegative3366 p) (nonnegative7852 p)
def d7854 (p : Pattern) : Int := if p 204 then d12 p else d7853 p
theorem agree7854 (p q : Pattern) (h : Agree support p q) : d7854 p = d7854 q := by
  simp only [d7854, h 204 (by decide), agree12 p q h, agree7853 p q h]
theorem nonnegative7854 (p : Pattern) : 0 ≤ d7854 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7853 p)
def d7855 (p : Pattern) : Int := if p 182 then d7854 p else d7851 p
theorem agree7855 (p q : Pattern) (h : Agree support p q) : d7855 p = d7855 q := by
  simp only [d7855, h 182 (by decide), agree7854 p q h, agree7851 p q h]
theorem nonnegative7855 (p : Pattern) : 0 ≤ d7855 p :=
  nonnegative_ite (p 182) (nonnegative7854 p) (nonnegative7851 p)
def d7856 (p : Pattern) : Int := if p 163 then d7855 p else d7812 p
theorem agree7856 (p q : Pattern) (h : Agree support p q) : d7856 p = d7856 q := by
  simp only [d7856, h 163 (by decide), agree7855 p q h, agree7812 p q h]
theorem nonnegative7856 (p : Pattern) : 0 ≤ d7856 p :=
  nonnegative_ite (p 163) (nonnegative7855 p) (nonnegative7812 p)
def d7857 (p : Pattern) : Int := if p 163 then d7733 p else d7819 p
theorem agree7857 (p q : Pattern) (h : Agree support p q) : d7857 p = d7857 q := by
  simp only [d7857, h 163 (by decide), agree7733 p q h, agree7819 p q h]
theorem nonnegative7857 (p : Pattern) : 0 ≤ d7857 p :=
  nonnegative_ite (p 163) (nonnegative7733 p) (nonnegative7819 p)
def d7858 (p : Pattern) : Int := if p 162 then d7857 p else d7856 p
theorem agree7858 (p q : Pattern) (h : Agree support p q) : d7858 p = d7858 q := by
  simp only [d7858, h 162 (by decide), agree7857 p q h, agree7856 p q h]
theorem nonnegative7858 (p : Pattern) : 0 ≤ d7858 p :=
  nonnegative_ite (p 162) (nonnegative7857 p) (nonnegative7856 p)
def d7859 (p : Pattern) : Int := if p 163 then d7736 p else d7819 p
theorem agree7859 (p q : Pattern) (h : Agree support p q) : d7859 p = d7859 q := by
  simp only [d7859, h 163 (by decide), agree7736 p q h, agree7819 p q h]
theorem nonnegative7859 (p : Pattern) : 0 ≤ d7859 p :=
  nonnegative_ite (p 163) (nonnegative7736 p) (nonnegative7819 p)
def d7860 (p : Pattern) : Int := if p 162 then d12 p else d7859 p
theorem agree7860 (p q : Pattern) (h : Agree support p q) : d7860 p = d7860 q := by
  simp only [d7860, h 162 (by decide), agree12 p q h, agree7859 p q h]
theorem nonnegative7860 (p : Pattern) : 0 ≤ d7860 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7859 p)
def d7861 (p : Pattern) : Int := if p 161 then d7860 p else d7858 p
theorem agree7861 (p q : Pattern) (h : Agree support p q) : d7861 p = d7861 q := by
  simp only [d7861, h 161 (by decide), agree7860 p q h, agree7858 p q h]
theorem nonnegative7861 (p : Pattern) : 0 ≤ d7861 p :=
  nonnegative_ite (p 161) (nonnegative7860 p) (nonnegative7858 p)
def d7862 (p : Pattern) : Int := if p 204 then d7831 p else d3374 p
theorem agree7862 (p q : Pattern) (h : Agree support p q) : d7862 p = d7862 q := by
  simp only [d7862, h 204 (by decide), agree7831 p q h, agree3374 p q h]
theorem nonnegative7862 (p : Pattern) : 0 ≤ d7862 p :=
  nonnegative_ite (p 204) (nonnegative7831 p) (nonnegative3374 p)
def d7863 (p : Pattern) : Int := if p 182 then d12 p else d7862 p
theorem agree7863 (p q : Pattern) (h : Agree support p q) : d7863 p = d7863 q := by
  simp only [d7863, h 182 (by decide), agree12 p q h, agree7862 p q h]
theorem nonnegative7863 (p : Pattern) : 0 ≤ d7863 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7862 p)
def d7864 (p : Pattern) : Int := if p 163 then d7863 p else d7836 p
theorem agree7864 (p q : Pattern) (h : Agree support p q) : d7864 p = d7864 q := by
  simp only [d7864, h 163 (by decide), agree7863 p q h, agree7836 p q h]
theorem nonnegative7864 (p : Pattern) : 0 ≤ d7864 p :=
  nonnegative_ite (p 163) (nonnegative7863 p) (nonnegative7836 p)
def d7865 (p : Pattern) : Int := if p 163 then d7745 p else d7842 p
theorem agree7865 (p q : Pattern) (h : Agree support p q) : d7865 p = d7865 q := by
  simp only [d7865, h 163 (by decide), agree7745 p q h, agree7842 p q h]
theorem nonnegative7865 (p : Pattern) : 0 ≤ d7865 p :=
  nonnegative_ite (p 163) (nonnegative7745 p) (nonnegative7842 p)
def d7866 (p : Pattern) : Int := if p 162 then d7865 p else d7864 p
theorem agree7866 (p q : Pattern) (h : Agree support p q) : d7866 p = d7866 q := by
  simp only [d7866, h 162 (by decide), agree7865 p q h, agree7864 p q h]
theorem nonnegative7866 (p : Pattern) : 0 ≤ d7866 p :=
  nonnegative_ite (p 162) (nonnegative7865 p) (nonnegative7864 p)
def d7867 (p : Pattern) : Int := if p 163 then d7747 p else d7842 p
theorem agree7867 (p q : Pattern) (h : Agree support p q) : d7867 p = d7867 q := by
  simp only [d7867, h 163 (by decide), agree7747 p q h, agree7842 p q h]
theorem nonnegative7867 (p : Pattern) : 0 ≤ d7867 p :=
  nonnegative_ite (p 163) (nonnegative7747 p) (nonnegative7842 p)
def d7868 (p : Pattern) : Int := if p 162 then d12 p else d7867 p
theorem agree7868 (p q : Pattern) (h : Agree support p q) : d7868 p = d7868 q := by
  simp only [d7868, h 162 (by decide), agree12 p q h, agree7867 p q h]
theorem nonnegative7868 (p : Pattern) : 0 ≤ d7868 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7867 p)
def d7869 (p : Pattern) : Int := if p 161 then d7868 p else d7866 p
theorem agree7869 (p q : Pattern) (h : Agree support p q) : d7869 p = d7869 q := by
  simp only [d7869, h 161 (by decide), agree7868 p q h, agree7866 p q h]
theorem nonnegative7869 (p : Pattern) : 0 ≤ d7869 p :=
  nonnegative_ite (p 161) (nonnegative7868 p) (nonnegative7866 p)
def d7870 (p : Pattern) : Int := if p 160 then d7869 p else d7861 p
theorem agree7870 (p q : Pattern) (h : Agree support p q) : d7870 p = d7870 q := by
  simp only [d7870, h 160 (by decide), agree7869 p q h, agree7861 p q h]
theorem nonnegative7870 (p : Pattern) : 0 ≤ d7870 p :=
  nonnegative_ite (p 160) (nonnegative7869 p) (nonnegative7861 p)
def d7871 (p : Pattern) : Int := if p 141 then d7870 p else d7848 p
theorem agree7871 (p q : Pattern) (h : Agree support p q) : d7871 p = d7871 q := by
  simp only [d7871, h 141 (by decide), agree7870 p q h, agree7848 p q h]
theorem nonnegative7871 (p : Pattern) : 0 ≤ d7871 p :=
  nonnegative_ite (p 141) (nonnegative7870 p) (nonnegative7848 p)
def d7872 (p : Pattern) : Int := if p 224 then d7816 p else d7825 p
theorem agree7872 (p q : Pattern) (h : Agree support p q) : d7872 p = d7872 q := by
  simp only [d7872, h 224 (by decide), agree7816 p q h, agree7825 p q h]
theorem nonnegative7872 (p : Pattern) : 0 ≤ d7872 p :=
  nonnegative_ite (p 224) (nonnegative7816 p) (nonnegative7825 p)
def d7873 (p : Pattern) : Int := if p 204 then d7872 p else d3358 p
theorem agree7873 (p q : Pattern) (h : Agree support p q) : d7873 p = d7873 q := by
  simp only [d7873, h 204 (by decide), agree7872 p q h, agree3358 p q h]
theorem nonnegative7873 (p : Pattern) : 0 ≤ d7873 p :=
  nonnegative_ite (p 204) (nonnegative7872 p) (nonnegative3358 p)
def d7874 (p : Pattern) : Int := if p 204 then d12 p else d7807 p
theorem agree7874 (p q : Pattern) (h : Agree support p q) : d7874 p = d7874 q := by
  simp only [d7874, h 204 (by decide), agree12 p q h, agree7807 p q h]
theorem nonnegative7874 (p : Pattern) : 0 ≤ d7874 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7807 p)
def d7875 (p : Pattern) : Int := if p 182 then d7874 p else d7873 p
theorem agree7875 (p q : Pattern) (h : Agree support p q) : d7875 p = d7875 q := by
  simp only [d7875, h 182 (by decide), agree7874 p q h, agree7873 p q h]
theorem nonnegative7875 (p : Pattern) : 0 ≤ d7875 p :=
  nonnegative_ite (p 182) (nonnegative7874 p) (nonnegative7873 p)
def d7876 (p : Pattern) : Int := if p 224 then d7839 p else d7825 p
theorem agree7876 (p q : Pattern) (h : Agree support p q) : d7876 p = d7876 q := by
  simp only [d7876, h 224 (by decide), agree7839 p q h, agree7825 p q h]
theorem nonnegative7876 (p : Pattern) : 0 ≤ d7876 p :=
  nonnegative_ite (p 224) (nonnegative7839 p) (nonnegative7825 p)
def d7877 (p : Pattern) : Int := if p 204 then d7876 p else d3358 p
theorem agree7877 (p q : Pattern) (h : Agree support p q) : d7877 p = d7877 q := by
  simp only [d7877, h 204 (by decide), agree7876 p q h, agree3358 p q h]
theorem nonnegative7877 (p : Pattern) : 0 ≤ d7877 p :=
  nonnegative_ite (p 204) (nonnegative7876 p) (nonnegative3358 p)
def d7878 (p : Pattern) : Int := if p 224 then d7813 p else d7825 p
theorem agree7878 (p q : Pattern) (h : Agree support p q) : d7878 p = d7878 q := by
  simp only [d7878, h 224 (by decide), agree7813 p q h, agree7825 p q h]
theorem nonnegative7878 (p : Pattern) : 0 ≤ d7878 p :=
  nonnegative_ite (p 224) (nonnegative7813 p) (nonnegative7825 p)
def d7879 (p : Pattern) : Int := if p 204 then d12 p else d7878 p
theorem agree7879 (p q : Pattern) (h : Agree support p q) : d7879 p = d7879 q := by
  simp only [d7879, h 204 (by decide), agree12 p q h, agree7878 p q h]
theorem nonnegative7879 (p : Pattern) : 0 ≤ d7879 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7878 p)
def d7880 (p : Pattern) : Int := if p 182 then d7879 p else d7877 p
theorem agree7880 (p q : Pattern) (h : Agree support p q) : d7880 p = d7880 q := by
  simp only [d7880, h 182 (by decide), agree7879 p q h, agree7877 p q h]
theorem nonnegative7880 (p : Pattern) : 0 ≤ d7880 p :=
  nonnegative_ite (p 182) (nonnegative7879 p) (nonnegative7877 p)
def d7881 (p : Pattern) : Int := if p 163 then d7880 p else d7875 p
theorem agree7881 (p q : Pattern) (h : Agree support p q) : d7881 p = d7881 q := by
  simp only [d7881, h 163 (by decide), agree7880 p q h, agree7875 p q h]
theorem nonnegative7881 (p : Pattern) : 0 ≤ d7881 p :=
  nonnegative_ite (p 163) (nonnegative7880 p) (nonnegative7875 p)
def d7882 (p : Pattern) : Int := if p 204 then d12 p else d7827 p
theorem agree7882 (p q : Pattern) (h : Agree support p q) : d7882 p = d7882 q := by
  simp only [d7882, h 204 (by decide), agree12 p q h, agree7827 p q h]
theorem nonnegative7882 (p : Pattern) : 0 ≤ d7882 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7827 p)
def d7883 (p : Pattern) : Int := if p 182 then d7882 p else d7828 p
theorem agree7883 (p q : Pattern) (h : Agree support p q) : d7883 p = d7883 q := by
  simp only [d7883, h 182 (by decide), agree7882 p q h, agree7828 p q h]
theorem nonnegative7883 (p : Pattern) : 0 ≤ d7883 p :=
  nonnegative_ite (p 182) (nonnegative7882 p) (nonnegative7828 p)
def d7884 (p : Pattern) : Int := if p 204 then d12 p else d7840 p
theorem agree7884 (p q : Pattern) (h : Agree support p q) : d7884 p = d7884 q := by
  simp only [d7884, h 204 (by decide), agree12 p q h, agree7840 p q h]
theorem nonnegative7884 (p : Pattern) : 0 ≤ d7884 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7840 p)
def d7885 (p : Pattern) : Int := if p 182 then d7884 p else d7841 p
theorem agree7885 (p q : Pattern) (h : Agree support p q) : d7885 p = d7885 q := by
  simp only [d7885, h 182 (by decide), agree7884 p q h, agree7841 p q h]
theorem nonnegative7885 (p : Pattern) : 0 ≤ d7885 p :=
  nonnegative_ite (p 182) (nonnegative7884 p) (nonnegative7841 p)
def d7886 (p : Pattern) : Int := if p 163 then d7885 p else d7883 p
theorem agree7886 (p q : Pattern) (h : Agree support p q) : d7886 p = d7886 q := by
  simp only [d7886, h 163 (by decide), agree7885 p q h, agree7883 p q h]
theorem nonnegative7886 (p : Pattern) : 0 ≤ d7886 p :=
  nonnegative_ite (p 163) (nonnegative7885 p) (nonnegative7883 p)
def d7887 (p : Pattern) : Int := if p 162 then d7886 p else d7881 p
theorem agree7887 (p q : Pattern) (h : Agree support p q) : d7887 p = d7887 q := by
  simp only [d7887, h 162 (by decide), agree7886 p q h, agree7881 p q h]
theorem nonnegative7887 (p : Pattern) : 0 ≤ d7887 p :=
  nonnegative_ite (p 162) (nonnegative7886 p) (nonnegative7881 p)
def d7888 (p : Pattern) : Int := if p 162 then d7822 p else d7886 p
theorem agree7888 (p q : Pattern) (h : Agree support p q) : d7888 p = d7888 q := by
  simp only [d7888, h 162 (by decide), agree7822 p q h, agree7886 p q h]
theorem nonnegative7888 (p : Pattern) : 0 ≤ d7888 p :=
  nonnegative_ite (p 162) (nonnegative7822 p) (nonnegative7886 p)
def d7889 (p : Pattern) : Int := if p 161 then d7888 p else d7887 p
theorem agree7889 (p q : Pattern) (h : Agree support p q) : d7889 p = d7889 q := by
  simp only [d7889, h 161 (by decide), agree7888 p q h, agree7887 p q h]
theorem nonnegative7889 (p : Pattern) : 0 ≤ d7889 p :=
  nonnegative_ite (p 161) (nonnegative7888 p) (nonnegative7887 p)
def d7890 (p : Pattern) : Int := if p 182 then d7832 p else d7862 p
theorem agree7890 (p q : Pattern) (h : Agree support p q) : d7890 p = d7890 q := by
  simp only [d7890, h 182 (by decide), agree7832 p q h, agree7862 p q h]
theorem nonnegative7890 (p : Pattern) : 0 ≤ d7890 p :=
  nonnegative_ite (p 182) (nonnegative7832 p) (nonnegative7862 p)
def d7891 (p : Pattern) : Int := if p 204 then d7834 p else d3377 p
theorem agree7891 (p q : Pattern) (h : Agree support p q) : d7891 p = d7891 q := by
  simp only [d7891, h 204 (by decide), agree7834 p q h, agree3377 p q h]
theorem nonnegative7891 (p : Pattern) : 0 ≤ d7891 p :=
  nonnegative_ite (p 204) (nonnegative7834 p) (nonnegative3377 p)
def d7892 (p : Pattern) : Int := if p 182 then d7835 p else d7891 p
theorem agree7892 (p q : Pattern) (h : Agree support p q) : d7892 p = d7892 q := by
  simp only [d7892, h 182 (by decide), agree7835 p q h, agree7891 p q h]
theorem nonnegative7892 (p : Pattern) : 0 ≤ d7892 p :=
  nonnegative_ite (p 182) (nonnegative7835 p) (nonnegative7891 p)
def d7893 (p : Pattern) : Int := if p 163 then d7892 p else d7890 p
theorem agree7893 (p q : Pattern) (h : Agree support p q) : d7893 p = d7893 q := by
  simp only [d7893, h 163 (by decide), agree7892 p q h, agree7890 p q h]
theorem nonnegative7893 (p : Pattern) : 0 ≤ d7893 p :=
  nonnegative_ite (p 163) (nonnegative7892 p) (nonnegative7890 p)
def d7894 (p : Pattern) : Int := if p 162 then d12 p else d7893 p
theorem agree7894 (p q : Pattern) (h : Agree support p q) : d7894 p = d7894 q := by
  simp only [d7894, h 162 (by decide), agree12 p q h, agree7893 p q h]
theorem nonnegative7894 (p : Pattern) : 0 ≤ d7894 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7893 p)
def d7895 (p : Pattern) : Int := if p 161 then d12 p else d7894 p
theorem agree7895 (p q : Pattern) (h : Agree support p q) : d7895 p = d7895 q := by
  simp only [d7895, h 161 (by decide), agree12 p q h, agree7894 p q h]
theorem nonnegative7895 (p : Pattern) : 0 ≤ d7895 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7894 p)
def d7896 (p : Pattern) : Int := if p 160 then d7895 p else d7889 p
theorem agree7896 (p q : Pattern) (h : Agree support p q) : d7896 p = d7896 q := by
  simp only [d7896, h 160 (by decide), agree7895 p q h, agree7889 p q h]
theorem nonnegative7896 (p : Pattern) : 0 ≤ d7896 p :=
  nonnegative_ite (p 160) (nonnegative7895 p) (nonnegative7889 p)
def d7897 (p : Pattern) : Int := if p 163 then d7890 p else d7880 p
theorem agree7897 (p q : Pattern) (h : Agree support p q) : d7897 p = d7897 q := by
  simp only [d7897, h 163 (by decide), agree7890 p q h, agree7880 p q h]
theorem nonnegative7897 (p : Pattern) : 0 ≤ d7897 p :=
  nonnegative_ite (p 163) (nonnegative7890 p) (nonnegative7880 p)
def d7898 (p : Pattern) : Int := if p 163 then d7733 p else d7885 p
theorem agree7898 (p q : Pattern) (h : Agree support p q) : d7898 p = d7898 q := by
  simp only [d7898, h 163 (by decide), agree7733 p q h, agree7885 p q h]
theorem nonnegative7898 (p : Pattern) : 0 ≤ d7898 p :=
  nonnegative_ite (p 163) (nonnegative7733 p) (nonnegative7885 p)
def d7899 (p : Pattern) : Int := if p 162 then d7898 p else d7897 p
theorem agree7899 (p q : Pattern) (h : Agree support p q) : d7899 p = d7899 q := by
  simp only [d7899, h 162 (by decide), agree7898 p q h, agree7897 p q h]
theorem nonnegative7899 (p : Pattern) : 0 ≤ d7899 p :=
  nonnegative_ite (p 162) (nonnegative7898 p) (nonnegative7897 p)
def d7900 (p : Pattern) : Int := if p 163 then d7736 p else d7885 p
theorem agree7900 (p q : Pattern) (h : Agree support p q) : d7900 p = d7900 q := by
  simp only [d7900, h 163 (by decide), agree7736 p q h, agree7885 p q h]
theorem nonnegative7900 (p : Pattern) : 0 ≤ d7900 p :=
  nonnegative_ite (p 163) (nonnegative7736 p) (nonnegative7885 p)
def d7901 (p : Pattern) : Int := if p 162 then d12 p else d7900 p
theorem agree7901 (p q : Pattern) (h : Agree support p q) : d7901 p = d7901 q := by
  simp only [d7901, h 162 (by decide), agree12 p q h, agree7900 p q h]
theorem nonnegative7901 (p : Pattern) : 0 ≤ d7901 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7900 p)
def d7902 (p : Pattern) : Int := if p 161 then d7901 p else d7899 p
theorem agree7902 (p q : Pattern) (h : Agree support p q) : d7902 p = d7902 q := by
  simp only [d7902, h 161 (by decide), agree7901 p q h, agree7899 p q h]
theorem nonnegative7902 (p : Pattern) : 0 ≤ d7902 p :=
  nonnegative_ite (p 161) (nonnegative7901 p) (nonnegative7899 p)
def d7903 (p : Pattern) : Int := if p 163 then d12 p else d7892 p
theorem agree7903 (p q : Pattern) (h : Agree support p q) : d7903 p = d7903 q := by
  simp only [d7903, h 163 (by decide), agree12 p q h, agree7892 p q h]
theorem nonnegative7903 (p : Pattern) : 0 ≤ d7903 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7892 p)
def d7904 (p : Pattern) : Int := if p 162 then d12 p else d7903 p
theorem agree7904 (p q : Pattern) (h : Agree support p q) : d7904 p = d7904 q := by
  simp only [d7904, h 162 (by decide), agree12 p q h, agree7903 p q h]
theorem nonnegative7904 (p : Pattern) : 0 ≤ d7904 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7903 p)
def d7905 (p : Pattern) : Int := if p 161 then d12 p else d7904 p
theorem agree7905 (p q : Pattern) (h : Agree support p q) : d7905 p = d7905 q := by
  simp only [d7905, h 161 (by decide), agree12 p q h, agree7904 p q h]
theorem nonnegative7905 (p : Pattern) : 0 ≤ d7905 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7904 p)
def d7906 (p : Pattern) : Int := if p 160 then d7905 p else d7902 p
theorem agree7906 (p q : Pattern) (h : Agree support p q) : d7906 p = d7906 q := by
  simp only [d7906, h 160 (by decide), agree7905 p q h, agree7902 p q h]
theorem nonnegative7906 (p : Pattern) : 0 ≤ d7906 p :=
  nonnegative_ite (p 160) (nonnegative7905 p) (nonnegative7902 p)
def d7907 (p : Pattern) : Int := if p 141 then d7906 p else d7896 p
theorem agree7907 (p q : Pattern) (h : Agree support p q) : d7907 p = d7907 q := by
  simp only [d7907, h 141 (by decide), agree7906 p q h, agree7896 p q h]
theorem nonnegative7907 (p : Pattern) : 0 ≤ d7907 p :=
  nonnegative_ite (p 141) (nonnegative7906 p) (nonnegative7896 p)
def d7908 (p : Pattern) : Int := if p 138 then d7907 p else d7871 p
theorem agree7908 (p q : Pattern) (h : Agree support p q) : d7908 p = d7908 q := by
  simp only [d7908, h 138 (by decide), agree7907 p q h, agree7871 p q h]
theorem nonnegative7908 (p : Pattern) : 0 ≤ d7908 p :=
  nonnegative_ite (p 138) (nonnegative7907 p) (nonnegative7871 p)
def d7909 (p : Pattern) : Int := if p 162 then d12 p else d7822 p
theorem agree7909 (p q : Pattern) (h : Agree support p q) : d7909 p = d7909 q := by
  simp only [d7909, h 162 (by decide), agree12 p q h, agree7822 p q h]
theorem nonnegative7909 (p : Pattern) : 0 ≤ d7909 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7822 p)
def d7910 (p : Pattern) : Int := if p 161 then d12 p else d7909 p
theorem agree7910 (p q : Pattern) (h : Agree support p q) : d7910 p = d7910 q := by
  simp only [d7910, h 161 (by decide), agree12 p q h, agree7909 p q h]
theorem nonnegative7910 (p : Pattern) : 0 ≤ d7910 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7909 p)
def d7911 (p : Pattern) : Int := if p 160 then d12 p else d7910 p
theorem agree7911 (p q : Pattern) (h : Agree support p q) : d7911 p = d7911 q := by
  simp only [d7911, h 160 (by decide), agree12 p q h, agree7910 p q h]
theorem nonnegative7911 (p : Pattern) : 0 ≤ d7911 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative7910 p)
def d7912 (p : Pattern) : Int := if p 141 then d12 p else d7911 p
theorem agree7912 (p q : Pattern) (h : Agree support p q) : d7912 p = d7912 q := by
  simp only [d7912, h 141 (by decide), agree12 p q h, agree7911 p q h]
theorem nonnegative7912 (p : Pattern) : 0 ≤ d7912 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative7911 p)
def d7913 (p : Pattern) : Int := if p 138 then d7912 p else d7907 p
theorem agree7913 (p q : Pattern) (h : Agree support p q) : d7913 p = d7913 q := by
  simp only [d7913, h 138 (by decide), agree7912 p q h, agree7907 p q h]
theorem nonnegative7913 (p : Pattern) : 0 ≤ d7913 p :=
  nonnegative_ite (p 138) (nonnegative7912 p) (nonnegative7907 p)
def d7914 (p : Pattern) : Int := if p 116 then d7913 p else d7908 p
theorem agree7914 (p q : Pattern) (h : Agree support p q) : d7914 p = d7914 q := by
  simp only [d7914, h 116 (by decide), agree7913 p q h, agree7908 p q h]
theorem nonnegative7914 (p : Pattern) : 0 ≤ d7914 p :=
  nonnegative_ite (p 116) (nonnegative7913 p) (nonnegative7908 p)
def d7915 (p : Pattern) : Int := if p 138 then d12 p else d7907 p
theorem agree7915 (p q : Pattern) (h : Agree support p q) : d7915 p = d7915 q := by
  simp only [d7915, h 138 (by decide), agree12 p q h, agree7907 p q h]
theorem nonnegative7915 (p : Pattern) : 0 ≤ d7915 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7907 p)
def d7916 (p : Pattern) : Int := if p 116 then d7915 p else d7908 p
theorem agree7916 (p q : Pattern) (h : Agree support p q) : d7916 p = d7916 q := by
  simp only [d7916, h 116 (by decide), agree7915 p q h, agree7908 p q h]
theorem nonnegative7916 (p : Pattern) : 0 ≤ d7916 p :=
  nonnegative_ite (p 116) (nonnegative7915 p) (nonnegative7908 p)
def d7917 (p : Pattern) : Int := if p 115 then d7916 p else d7914 p
theorem agree7917 (p q : Pattern) (h : Agree support p q) : d7917 p = d7917 q := by
  simp only [d7917, h 115 (by decide), agree7916 p q h, agree7914 p q h]
theorem nonnegative7917 (p : Pattern) : 0 ≤ d7917 p :=
  nonnegative_ite (p 115) (nonnegative7916 p) (nonnegative7914 p)
def d7918 (p : Pattern) : Int := if p 71 then d7917 p else d7805 p
theorem agree7918 (p q : Pattern) (h : Agree support p q) : d7918 p = d7918 q := by
  simp only [d7918, h 71 (by decide), agree7917 p q h, agree7805 p q h]
theorem nonnegative7918 (p : Pattern) : 0 ≤ d7918 p :=
  nonnegative_ite (p 71) (nonnegative7917 p) (nonnegative7805 p)
def d7919 (p : Pattern) : Int := if p 49 then d7918 p else d7805 p
theorem agree7919 (p q : Pattern) (h : Agree support p q) : d7919 p = d7919 q := by
  simp only [d7919, h 49 (by decide), agree7918 p q h, agree7805 p q h]
theorem nonnegative7919 (p : Pattern) : 0 ≤ d7919 p :=
  nonnegative_ite (p 49) (nonnegative7918 p) (nonnegative7805 p)
end NetHack.Sokoban22Refined85
