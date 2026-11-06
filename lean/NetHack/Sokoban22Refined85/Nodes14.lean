/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1680 (p : Pattern) : Int := if p 49 then d1679 p else d1639 p
theorem agree1680 (p q : Pattern) (h : Agree support p q) : d1680 p = d1680 q := by
  simp only [d1680, h 49 (by decide), agree1679 p q h, agree1639 p q h]
theorem nonnegative1680 (p : Pattern) : 0 ≤ d1680 p :=
  nonnegative_ite (p 49) (nonnegative1679 p) (nonnegative1639 p)
def d1681 (p : Pattern) : Int := if p 48 then d1680 p else d1611 p
theorem agree1681 (p q : Pattern) (h : Agree support p q) : d1681 p = d1681 q := by
  simp only [d1681, h 48 (by decide), agree1680 p q h, agree1611 p q h]
theorem nonnegative1681 (p : Pattern) : 0 ≤ d1681 p :=
  nonnegative_ite (p 48) (nonnegative1680 p) (nonnegative1611 p)
def d1682 (p : Pattern) : Int := if p 204 then d321 p else d14 p
theorem agree1682 (p q : Pattern) (h : Agree support p q) : d1682 p = d1682 q := by
  simp only [d1682, h 204 (by decide), agree321 p q h, agree14 p q h]
theorem nonnegative1682 (p : Pattern) : 0 ≤ d1682 p :=
  nonnegative_ite (p 204) (nonnegative321 p) (nonnegative14 p)
def d1683 (p : Pattern) : Int := if p 247 then d2 p else d0 p
theorem agree1683 (p q : Pattern) (h : Agree support p q) : d1683 p = d1683 q := by
  simp only [d1683, h 247 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative1683 (p : Pattern) : 0 ≤ d1683 p :=
  nonnegative_ite (p 247) (nonnegative2 p) (nonnegative0 p)
def d1684 (p : Pattern) : Int := if p 246 then d30 p else d1683 p
theorem agree1684 (p q : Pattern) (h : Agree support p q) : d1684 p = d1684 q := by
  simp only [d1684, h 246 (by decide), agree30 p q h, agree1683 p q h]
theorem nonnegative1684 (p : Pattern) : 0 ≤ d1684 p :=
  nonnegative_ite (p 246) (nonnegative30 p) (nonnegative1683 p)
def d1685 (p : Pattern) : Int := if p 225 then d1684 p else d14 p
theorem agree1685 (p q : Pattern) (h : Agree support p q) : d1685 p = d1685 q := by
  simp only [d1685, h 225 (by decide), agree1684 p q h, agree14 p q h]
theorem nonnegative1685 (p : Pattern) : 0 ≤ d1685 p :=
  nonnegative_ite (p 225) (nonnegative1684 p) (nonnegative14 p)
def d1686 (p : Pattern) : Int := if p 224 then d1684 p else d1685 p
theorem agree1686 (p q : Pattern) (h : Agree support p q) : d1686 p = d1686 q := by
  simp only [d1686, h 224 (by decide), agree1684 p q h, agree1685 p q h]
theorem nonnegative1686 (p : Pattern) : 0 ≤ d1686 p :=
  nonnegative_ite (p 224) (nonnegative1684 p) (nonnegative1685 p)
def d1687 (p : Pattern) : Int := if p 204 then d12 p else d1686 p
theorem agree1687 (p q : Pattern) (h : Agree support p q) : d1687 p = d1687 q := by
  simp only [d1687, h 204 (by decide), agree12 p q h, agree1686 p q h]
theorem nonnegative1687 (p : Pattern) : 0 ≤ d1687 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1686 p)
def d1688 (p : Pattern) : Int := if p 182 then d1687 p else d1682 p
theorem agree1688 (p q : Pattern) (h : Agree support p q) : d1688 p = d1688 q := by
  simp only [d1688, h 182 (by decide), agree1687 p q h, agree1682 p q h]
theorem nonnegative1688 (p : Pattern) : 0 ≤ d1688 p :=
  nonnegative_ite (p 182) (nonnegative1687 p) (nonnegative1682 p)
def d1689 (p : Pattern) : Int := if p 204 then d333 p else d14 p
theorem agree1689 (p q : Pattern) (h : Agree support p q) : d1689 p = d1689 q := by
  simp only [d1689, h 204 (by decide), agree333 p q h, agree14 p q h]
theorem nonnegative1689 (p : Pattern) : 0 ≤ d1689 p :=
  nonnegative_ite (p 204) (nonnegative333 p) (nonnegative14 p)
def d1690 (p : Pattern) : Int := if p 182 then d1687 p else d1689 p
theorem agree1690 (p q : Pattern) (h : Agree support p q) : d1690 p = d1690 q := by
  simp only [d1690, h 182 (by decide), agree1687 p q h, agree1689 p q h]
theorem nonnegative1690 (p : Pattern) : 0 ≤ d1690 p :=
  nonnegative_ite (p 182) (nonnegative1687 p) (nonnegative1689 p)
def d1691 (p : Pattern) : Int := if p 163 then d1690 p else d1688 p
theorem agree1691 (p q : Pattern) (h : Agree support p q) : d1691 p = d1691 q := by
  simp only [d1691, h 163 (by decide), agree1690 p q h, agree1688 p q h]
theorem nonnegative1691 (p : Pattern) : 0 ≤ d1691 p :=
  nonnegative_ite (p 163) (nonnegative1690 p) (nonnegative1688 p)
def d1692 (p : Pattern) : Int := if p 182 then d1687 p else d15 p
theorem agree1692 (p q : Pattern) (h : Agree support p q) : d1692 p = d1692 q := by
  simp only [d1692, h 182 (by decide), agree1687 p q h, agree15 p q h]
theorem nonnegative1692 (p : Pattern) : 0 ≤ d1692 p :=
  nonnegative_ite (p 182) (nonnegative1687 p) (nonnegative15 p)
def d1693 (p : Pattern) : Int := if p 247 then d6 p else d4 p
theorem agree1693 (p q : Pattern) (h : Agree support p q) : d1693 p = d1693 q := by
  simp only [d1693, h 247 (by decide), agree6 p q h, agree4 p q h]
theorem nonnegative1693 (p : Pattern) : 0 ≤ d1693 p :=
  nonnegative_ite (p 247) (nonnegative6 p) (nonnegative4 p)
def d1694 (p : Pattern) : Int := if p 246 then d34 p else d1693 p
theorem agree1694 (p q : Pattern) (h : Agree support p q) : d1694 p = d1694 q := by
  simp only [d1694, h 246 (by decide), agree34 p q h, agree1693 p q h]
theorem nonnegative1694 (p : Pattern) : 0 ≤ d1694 p :=
  nonnegative_ite (p 246) (nonnegative34 p) (nonnegative1693 p)
def d1695 (p : Pattern) : Int := if p 225 then d1694 p else d18 p
theorem agree1695 (p q : Pattern) (h : Agree support p q) : d1695 p = d1695 q := by
  simp only [d1695, h 225 (by decide), agree1694 p q h, agree18 p q h]
theorem nonnegative1695 (p : Pattern) : 0 ≤ d1695 p :=
  nonnegative_ite (p 225) (nonnegative1694 p) (nonnegative18 p)
def d1696 (p : Pattern) : Int := if p 224 then d1694 p else d1695 p
theorem agree1696 (p q : Pattern) (h : Agree support p q) : d1696 p = d1696 q := by
  simp only [d1696, h 224 (by decide), agree1694 p q h, agree1695 p q h]
theorem nonnegative1696 (p : Pattern) : 0 ≤ d1696 p :=
  nonnegative_ite (p 224) (nonnegative1694 p) (nonnegative1695 p)
def d1697 (p : Pattern) : Int := if p 204 then d12 p else d1696 p
theorem agree1697 (p q : Pattern) (h : Agree support p q) : d1697 p = d1697 q := by
  simp only [d1697, h 204 (by decide), agree12 p q h, agree1696 p q h]
theorem nonnegative1697 (p : Pattern) : 0 ≤ d1697 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1696 p)
def d1698 (p : Pattern) : Int := if p 182 then d1697 p else d19 p
theorem agree1698 (p q : Pattern) (h : Agree support p q) : d1698 p = d1698 q := by
  simp only [d1698, h 182 (by decide), agree1697 p q h, agree19 p q h]
theorem nonnegative1698 (p : Pattern) : 0 ≤ d1698 p :=
  nonnegative_ite (p 182) (nonnegative1697 p) (nonnegative19 p)
def d1699 (p : Pattern) : Int := if p 163 then d1698 p else d1692 p
theorem agree1699 (p q : Pattern) (h : Agree support p q) : d1699 p = d1699 q := by
  simp only [d1699, h 163 (by decide), agree1698 p q h, agree1692 p q h]
theorem nonnegative1699 (p : Pattern) : 0 ≤ d1699 p :=
  nonnegative_ite (p 163) (nonnegative1698 p) (nonnegative1692 p)
def d1700 (p : Pattern) : Int := if p 162 then d1699 p else d1691 p
theorem agree1700 (p q : Pattern) (h : Agree support p q) : d1700 p = d1700 q := by
  simp only [d1700, h 162 (by decide), agree1699 p q h, agree1691 p q h]
theorem nonnegative1700 (p : Pattern) : 0 ≤ d1700 p :=
  nonnegative_ite (p 162) (nonnegative1699 p) (nonnegative1691 p)
def d1701 (p : Pattern) : Int := if p 247 then d11 p else d9 p
theorem agree1701 (p q : Pattern) (h : Agree support p q) : d1701 p = d1701 q := by
  simp only [d1701, h 247 (by decide), agree11 p q h, agree9 p q h]
theorem nonnegative1701 (p : Pattern) : 0 ≤ d1701 p :=
  nonnegative_ite (p 247) (nonnegative11 p) (nonnegative9 p)
def d1702 (p : Pattern) : Int := if p 246 then d39 p else d1701 p
theorem agree1702 (p q : Pattern) (h : Agree support p q) : d1702 p = d1702 q := by
  simp only [d1702, h 246 (by decide), agree39 p q h, agree1701 p q h]
theorem nonnegative1702 (p : Pattern) : 0 ≤ d1702 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative1701 p)
def d1703 (p : Pattern) : Int := if p 225 then d1702 p else d24 p
theorem agree1703 (p q : Pattern) (h : Agree support p q) : d1703 p = d1703 q := by
  simp only [d1703, h 225 (by decide), agree1702 p q h, agree24 p q h]
theorem nonnegative1703 (p : Pattern) : 0 ≤ d1703 p :=
  nonnegative_ite (p 225) (nonnegative1702 p) (nonnegative24 p)
def d1704 (p : Pattern) : Int := if p 224 then d1702 p else d1703 p
theorem agree1704 (p q : Pattern) (h : Agree support p q) : d1704 p = d1704 q := by
  simp only [d1704, h 224 (by decide), agree1702 p q h, agree1703 p q h]
theorem nonnegative1704 (p : Pattern) : 0 ≤ d1704 p :=
  nonnegative_ite (p 224) (nonnegative1702 p) (nonnegative1703 p)
def d1705 (p : Pattern) : Int := if p 204 then d12 p else d1704 p
theorem agree1705 (p q : Pattern) (h : Agree support p q) : d1705 p = d1705 q := by
  simp only [d1705, h 204 (by decide), agree12 p q h, agree1704 p q h]
theorem nonnegative1705 (p : Pattern) : 0 ≤ d1705 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1704 p)
def d1706 (p : Pattern) : Int := if p 182 then d1705 p else d25 p
theorem agree1706 (p q : Pattern) (h : Agree support p q) : d1706 p = d1706 q := by
  simp only [d1706, h 182 (by decide), agree1705 p q h, agree25 p q h]
theorem nonnegative1706 (p : Pattern) : 0 ≤ d1706 p :=
  nonnegative_ite (p 182) (nonnegative1705 p) (nonnegative25 p)
def d1707 (p : Pattern) : Int := if p 163 then d12 p else d1706 p
theorem agree1707 (p q : Pattern) (h : Agree support p q) : d1707 p = d1707 q := by
  simp only [d1707, h 163 (by decide), agree12 p q h, agree1706 p q h]
theorem nonnegative1707 (p : Pattern) : 0 ≤ d1707 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1706 p)
def d1708 (p : Pattern) : Int := if p 162 then d1707 p else d1699 p
theorem agree1708 (p q : Pattern) (h : Agree support p q) : d1708 p = d1708 q := by
  simp only [d1708, h 162 (by decide), agree1707 p q h, agree1699 p q h]
theorem nonnegative1708 (p : Pattern) : 0 ≤ d1708 p :=
  nonnegative_ite (p 162) (nonnegative1707 p) (nonnegative1699 p)
def d1709 (p : Pattern) : Int := if p 161 then d1708 p else d1700 p
theorem agree1709 (p q : Pattern) (h : Agree support p q) : d1709 p = d1709 q := by
  simp only [d1709, h 161 (by decide), agree1708 p q h, agree1700 p q h]
theorem nonnegative1709 (p : Pattern) : 0 ≤ d1709 p :=
  nonnegative_ite (p 161) (nonnegative1708 p) (nonnegative1700 p)
def d1710 (p : Pattern) : Int := if p 247 then d8 p else d2 p
theorem agree1710 (p q : Pattern) (h : Agree support p q) : d1710 p = d1710 q := by
  simp only [d1710, h 247 (by decide), agree8 p q h, agree2 p q h]
theorem nonnegative1710 (p : Pattern) : 0 ≤ d1710 p :=
  nonnegative_ite (p 247) (nonnegative8 p) (nonnegative2 p)
def d1711 (p : Pattern) : Int := if p 246 then d190 p else d1710 p
theorem agree1711 (p q : Pattern) (h : Agree support p q) : d1711 p = d1711 q := by
  simp only [d1711, h 246 (by decide), agree190 p q h, agree1710 p q h]
theorem nonnegative1711 (p : Pattern) : 0 ≤ d1711 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative1710 p)
def d1712 (p : Pattern) : Int := if p 225 then d1711 p else d31 p
theorem agree1712 (p q : Pattern) (h : Agree support p q) : d1712 p = d1712 q := by
  simp only [d1712, h 225 (by decide), agree1711 p q h, agree31 p q h]
theorem nonnegative1712 (p : Pattern) : 0 ≤ d1712 p :=
  nonnegative_ite (p 225) (nonnegative1711 p) (nonnegative31 p)
def d1713 (p : Pattern) : Int := if p 247 then d6 p else d2 p
theorem agree1713 (p q : Pattern) (h : Agree support p q) : d1713 p = d1713 q := by
  simp only [d1713, h 247 (by decide), agree6 p q h, agree2 p q h]
theorem nonnegative1713 (p : Pattern) : 0 ≤ d1713 p :=
  nonnegative_ite (p 247) (nonnegative6 p) (nonnegative2 p)
def d1714 (p : Pattern) : Int := if p 246 then d34 p else d1713 p
theorem agree1714 (p q : Pattern) (h : Agree support p q) : d1714 p = d1714 q := by
  simp only [d1714, h 246 (by decide), agree34 p q h, agree1713 p q h]
theorem nonnegative1714 (p : Pattern) : 0 ≤ d1714 p :=
  nonnegative_ite (p 246) (nonnegative34 p) (nonnegative1713 p)
def d1715 (p : Pattern) : Int := if p 246 then d39 p else d30 p
theorem agree1715 (p q : Pattern) (h : Agree support p q) : d1715 p = d1715 q := by
  simp only [d1715, h 246 (by decide), agree39 p q h, agree30 p q h]
theorem nonnegative1715 (p : Pattern) : 0 ≤ d1715 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative30 p)
def d1716 (p : Pattern) : Int := if p 225 then d1715 p else d1714 p
theorem agree1716 (p q : Pattern) (h : Agree support p q) : d1716 p = d1716 q := by
  simp only [d1716, h 225 (by decide), agree1715 p q h, agree1714 p q h]
theorem nonnegative1716 (p : Pattern) : 0 ≤ d1716 p :=
  nonnegative_ite (p 225) (nonnegative1715 p) (nonnegative1714 p)
def d1717 (p : Pattern) : Int := if p 224 then d1716 p else d1712 p
theorem agree1717 (p q : Pattern) (h : Agree support p q) : d1717 p = d1717 q := by
  simp only [d1717, h 224 (by decide), agree1716 p q h, agree1712 p q h]
theorem nonnegative1717 (p : Pattern) : 0 ≤ d1717 p :=
  nonnegative_ite (p 224) (nonnegative1716 p) (nonnegative1712 p)
def d1718 (p : Pattern) : Int := if p 204 then d12 p else d1717 p
theorem agree1718 (p q : Pattern) (h : Agree support p q) : d1718 p = d1718 q := by
  simp only [d1718, h 204 (by decide), agree12 p q h, agree1717 p q h]
theorem nonnegative1718 (p : Pattern) : 0 ≤ d1718 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1717 p)
def d1719 (p : Pattern) : Int := if p 182 then d1718 p else d15 p
theorem agree1719 (p q : Pattern) (h : Agree support p q) : d1719 p = d1719 q := by
  simp only [d1719, h 182 (by decide), agree1718 p q h, agree15 p q h]
theorem nonnegative1719 (p : Pattern) : 0 ≤ d1719 p :=
  nonnegative_ite (p 182) (nonnegative1718 p) (nonnegative15 p)
def d1720 (p : Pattern) : Int := if p 225 then d364 p else d35 p
theorem agree1720 (p q : Pattern) (h : Agree support p q) : d1720 p = d1720 q := by
  simp only [d1720, h 225 (by decide), agree364 p q h, agree35 p q h]
theorem nonnegative1720 (p : Pattern) : 0 ≤ d1720 p :=
  nonnegative_ite (p 225) (nonnegative364 p) (nonnegative35 p)
def d1721 (p : Pattern) : Int := if p 247 then d10 p else d6 p
theorem agree1721 (p q : Pattern) (h : Agree support p q) : d1721 p = d1721 q := by
  simp only [d1721, h 247 (by decide), agree10 p q h, agree6 p q h]
theorem nonnegative1721 (p : Pattern) : 0 ≤ d1721 p :=
  nonnegative_ite (p 247) (nonnegative10 p) (nonnegative6 p)
def d1722 (p : Pattern) : Int := if p 246 then d57 p else d1721 p
theorem agree1722 (p q : Pattern) (h : Agree support p q) : d1722 p = d1722 q := by
  simp only [d1722, h 246 (by decide), agree57 p q h, agree1721 p q h]
theorem nonnegative1722 (p : Pattern) : 0 ≤ d1722 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative1721 p)
def d1723 (p : Pattern) : Int := if p 225 then d364 p else d1722 p
theorem agree1723 (p q : Pattern) (h : Agree support p q) : d1723 p = d1723 q := by
  simp only [d1723, h 225 (by decide), agree364 p q h, agree1722 p q h]
theorem nonnegative1723 (p : Pattern) : 0 ≤ d1723 p :=
  nonnegative_ite (p 225) (nonnegative364 p) (nonnegative1722 p)
def d1724 (p : Pattern) : Int := if p 224 then d1723 p else d1720 p
theorem agree1724 (p q : Pattern) (h : Agree support p q) : d1724 p = d1724 q := by
  simp only [d1724, h 224 (by decide), agree1723 p q h, agree1720 p q h]
theorem nonnegative1724 (p : Pattern) : 0 ≤ d1724 p :=
  nonnegative_ite (p 224) (nonnegative1723 p) (nonnegative1720 p)
def d1725 (p : Pattern) : Int := if p 204 then d12 p else d1724 p
theorem agree1725 (p q : Pattern) (h : Agree support p q) : d1725 p = d1725 q := by
  simp only [d1725, h 204 (by decide), agree12 p q h, agree1724 p q h]
theorem nonnegative1725 (p : Pattern) : 0 ≤ d1725 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1724 p)
def d1726 (p : Pattern) : Int := if p 182 then d1725 p else d15 p
theorem agree1726 (p q : Pattern) (h : Agree support p q) : d1726 p = d1726 q := by
  simp only [d1726, h 182 (by decide), agree1725 p q h, agree15 p q h]
theorem nonnegative1726 (p : Pattern) : 0 ≤ d1726 p :=
  nonnegative_ite (p 182) (nonnegative1725 p) (nonnegative15 p)
def d1727 (p : Pattern) : Int := if p 163 then d1726 p else d1719 p
theorem agree1727 (p q : Pattern) (h : Agree support p q) : d1727 p = d1727 q := by
  simp only [d1727, h 163 (by decide), agree1726 p q h, agree1719 p q h]
theorem nonnegative1727 (p : Pattern) : 0 ≤ d1727 p :=
  nonnegative_ite (p 163) (nonnegative1726 p) (nonnegative1719 p)
def d1728 (p : Pattern) : Int := if p 225 then d327 p else d40 p
theorem agree1728 (p q : Pattern) (h : Agree support p q) : d1728 p = d1728 q := by
  simp only [d1728, h 225 (by decide), agree327 p q h, agree40 p q h]
theorem nonnegative1728 (p : Pattern) : 0 ≤ d1728 p :=
  nonnegative_ite (p 225) (nonnegative327 p) (nonnegative40 p)
def d1729 (p : Pattern) : Int := if p 224 then d327 p else d1728 p
theorem agree1729 (p q : Pattern) (h : Agree support p q) : d1729 p = d1729 q := by
  simp only [d1729, h 224 (by decide), agree327 p q h, agree1728 p q h]
theorem nonnegative1729 (p : Pattern) : 0 ≤ d1729 p :=
  nonnegative_ite (p 224) (nonnegative327 p) (nonnegative1728 p)
def d1730 (p : Pattern) : Int := if p 204 then d12 p else d1729 p
theorem agree1730 (p q : Pattern) (h : Agree support p q) : d1730 p = d1730 q := by
  simp only [d1730, h 204 (by decide), agree12 p q h, agree1729 p q h]
theorem nonnegative1730 (p : Pattern) : 0 ≤ d1730 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1729 p)
def d1731 (p : Pattern) : Int := if p 182 then d1730 p else d15 p
theorem agree1731 (p q : Pattern) (h : Agree support p q) : d1731 p = d1731 q := by
  simp only [d1731, h 182 (by decide), agree1730 p q h, agree15 p q h]
theorem nonnegative1731 (p : Pattern) : 0 ≤ d1731 p :=
  nonnegative_ite (p 182) (nonnegative1730 p) (nonnegative15 p)
def d1732 (p : Pattern) : Int := if p 182 then d12 p else d19 p
theorem agree1732 (p q : Pattern) (h : Agree support p q) : d1732 p = d1732 q := by
  simp only [d1732, h 182 (by decide), agree12 p q h, agree19 p q h]
theorem nonnegative1732 (p : Pattern) : 0 ≤ d1732 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative19 p)
def d1733 (p : Pattern) : Int := if p 163 then d1732 p else d1731 p
theorem agree1733 (p q : Pattern) (h : Agree support p q) : d1733 p = d1733 q := by
  simp only [d1733, h 163 (by decide), agree1732 p q h, agree1731 p q h]
theorem nonnegative1733 (p : Pattern) : 0 ≤ d1733 p :=
  nonnegative_ite (p 163) (nonnegative1732 p) (nonnegative1731 p)
def d1734 (p : Pattern) : Int := if p 162 then d1733 p else d1727 p
theorem agree1734 (p q : Pattern) (h : Agree support p q) : d1734 p = d1734 q := by
  simp only [d1734, h 162 (by decide), agree1733 p q h, agree1727 p q h]
theorem nonnegative1734 (p : Pattern) : 0 ≤ d1734 p :=
  nonnegative_ite (p 162) (nonnegative1733 p) (nonnegative1727 p)
def d1735 (p : Pattern) : Int := if p 182 then d12 p else d15 p
theorem agree1735 (p q : Pattern) (h : Agree support p q) : d1735 p = d1735 q := by
  simp only [d1735, h 182 (by decide), agree12 p q h, agree15 p q h]
theorem nonnegative1735 (p : Pattern) : 0 ≤ d1735 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative15 p)
def d1736 (p : Pattern) : Int := if p 163 then d1732 p else d1735 p
theorem agree1736 (p q : Pattern) (h : Agree support p q) : d1736 p = d1736 q := by
  simp only [d1736, h 163 (by decide), agree1732 p q h, agree1735 p q h]
theorem nonnegative1736 (p : Pattern) : 0 ≤ d1736 p :=
  nonnegative_ite (p 163) (nonnegative1732 p) (nonnegative1735 p)
def d1737 (p : Pattern) : Int := if p 162 then d528 p else d1736 p
theorem agree1737 (p q : Pattern) (h : Agree support p q) : d1737 p = d1737 q := by
  simp only [d1737, h 162 (by decide), agree528 p q h, agree1736 p q h]
theorem nonnegative1737 (p : Pattern) : 0 ≤ d1737 p :=
  nonnegative_ite (p 162) (nonnegative528 p) (nonnegative1736 p)
def d1738 (p : Pattern) : Int := if p 161 then d1737 p else d1734 p
theorem agree1738 (p q : Pattern) (h : Agree support p q) : d1738 p = d1738 q := by
  simp only [d1738, h 161 (by decide), agree1737 p q h, agree1734 p q h]
theorem nonnegative1738 (p : Pattern) : 0 ≤ d1738 p :=
  nonnegative_ite (p 161) (nonnegative1737 p) (nonnegative1734 p)
def d1739 (p : Pattern) : Int := if p 160 then d1738 p else d1709 p
theorem agree1739 (p q : Pattern) (h : Agree support p q) : d1739 p = d1739 q := by
  simp only [d1739, h 160 (by decide), agree1738 p q h, agree1709 p q h]
theorem nonnegative1739 (p : Pattern) : 0 ≤ d1739 p :=
  nonnegative_ite (p 160) (nonnegative1738 p) (nonnegative1709 p)
def d1740 (p : Pattern) : Int := if p 204 then d335 p else d14 p
theorem agree1740 (p q : Pattern) (h : Agree support p q) : d1740 p = d1740 q := by
  simp only [d1740, h 204 (by decide), agree335 p q h, agree14 p q h]
theorem nonnegative1740 (p : Pattern) : 0 ≤ d1740 p :=
  nonnegative_ite (p 204) (nonnegative335 p) (nonnegative14 p)
def d1741 (p : Pattern) : Int := if p 182 then d1687 p else d1740 p
theorem agree1741 (p q : Pattern) (h : Agree support p q) : d1741 p = d1741 q := by
  simp only [d1741, h 182 (by decide), agree1687 p q h, agree1740 p q h]
theorem nonnegative1741 (p : Pattern) : 0 ≤ d1741 p :=
  nonnegative_ite (p 182) (nonnegative1687 p) (nonnegative1740 p)
def d1742 (p : Pattern) : Int := if p 247 then d4 p else d2 p
theorem agree1742 (p q : Pattern) (h : Agree support p q) : d1742 p = d1742 q := by
  simp only [d1742, h 247 (by decide), agree4 p q h, agree2 p q h]
theorem nonnegative1742 (p : Pattern) : 0 ≤ d1742 p :=
  nonnegative_ite (p 247) (nonnegative4 p) (nonnegative2 p)
def d1743 (p : Pattern) : Int := if p 246 then d17 p else d1742 p
theorem agree1743 (p q : Pattern) (h : Agree support p q) : d1743 p = d1743 q := by
  simp only [d1743, h 246 (by decide), agree17 p q h, agree1742 p q h]
theorem nonnegative1743 (p : Pattern) : 0 ≤ d1743 p :=
  nonnegative_ite (p 246) (nonnegative17 p) (nonnegative1742 p)
def d1744 (p : Pattern) : Int := if p 225 then d1743 p else d31 p
theorem agree1744 (p q : Pattern) (h : Agree support p q) : d1744 p = d1744 q := by
  simp only [d1744, h 225 (by decide), agree1743 p q h, agree31 p q h]
theorem nonnegative1744 (p : Pattern) : 0 ≤ d1744 p :=
  nonnegative_ite (p 225) (nonnegative1743 p) (nonnegative31 p)
def d1745 (p : Pattern) : Int := if p 224 then d1743 p else d1744 p
theorem agree1745 (p q : Pattern) (h : Agree support p q) : d1745 p = d1745 q := by
  simp only [d1745, h 224 (by decide), agree1743 p q h, agree1744 p q h]
theorem nonnegative1745 (p : Pattern) : 0 ≤ d1745 p :=
  nonnegative_ite (p 224) (nonnegative1743 p) (nonnegative1744 p)
def d1746 (p : Pattern) : Int := if p 204 then d12 p else d1745 p
theorem agree1746 (p q : Pattern) (h : Agree support p q) : d1746 p = d1746 q := by
  simp only [d1746, h 204 (by decide), agree12 p q h, agree1745 p q h]
theorem nonnegative1746 (p : Pattern) : 0 ≤ d1746 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1745 p)
def d1747 (p : Pattern) : Int := if p 182 then d1746 p else d32 p
theorem agree1747 (p q : Pattern) (h : Agree support p q) : d1747 p = d1747 q := by
  simp only [d1747, h 182 (by decide), agree1746 p q h, agree32 p q h]
theorem nonnegative1747 (p : Pattern) : 0 ≤ d1747 p :=
  nonnegative_ite (p 182) (nonnegative1746 p) (nonnegative32 p)
def d1748 (p : Pattern) : Int := if p 163 then d1747 p else d1741 p
theorem agree1748 (p q : Pattern) (h : Agree support p q) : d1748 p = d1748 q := by
  simp only [d1748, h 163 (by decide), agree1747 p q h, agree1741 p q h]
theorem nonnegative1748 (p : Pattern) : 0 ≤ d1748 p :=
  nonnegative_ite (p 163) (nonnegative1747 p) (nonnegative1741 p)
def d1749 (p : Pattern) : Int := if p 163 then d1706 p else d1698 p
theorem agree1749 (p q : Pattern) (h : Agree support p q) : d1749 p = d1749 q := by
  simp only [d1749, h 163 (by decide), agree1706 p q h, agree1698 p q h]
theorem nonnegative1749 (p : Pattern) : 0 ≤ d1749 p :=
  nonnegative_ite (p 163) (nonnegative1706 p) (nonnegative1698 p)
def d1750 (p : Pattern) : Int := if p 162 then d1749 p else d1748 p
theorem agree1750 (p q : Pattern) (h : Agree support p q) : d1750 p = d1750 q := by
  simp only [d1750, h 162 (by decide), agree1749 p q h, agree1748 p q h]
theorem nonnegative1750 (p : Pattern) : 0 ≤ d1750 p :=
  nonnegative_ite (p 162) (nonnegative1749 p) (nonnegative1748 p)
def d1751 (p : Pattern) : Int := if p 225 then d329 p else d58 p
theorem agree1751 (p q : Pattern) (h : Agree support p q) : d1751 p = d1751 q := by
  simp only [d1751, h 225 (by decide), agree329 p q h, agree58 p q h]
theorem nonnegative1751 (p : Pattern) : 0 ≤ d1751 p :=
  nonnegative_ite (p 225) (nonnegative329 p) (nonnegative58 p)
def d1752 (p : Pattern) : Int := if p 224 then d329 p else d1751 p
theorem agree1752 (p q : Pattern) (h : Agree support p q) : d1752 p = d1752 q := by
  simp only [d1752, h 224 (by decide), agree329 p q h, agree1751 p q h]
theorem nonnegative1752 (p : Pattern) : 0 ≤ d1752 p :=
  nonnegative_ite (p 224) (nonnegative329 p) (nonnegative1751 p)
def d1753 (p : Pattern) : Int := if p 204 then d12 p else d1752 p
theorem agree1753 (p q : Pattern) (h : Agree support p q) : d1753 p = d1753 q := by
  simp only [d1753, h 204 (by decide), agree12 p q h, agree1752 p q h]
theorem nonnegative1753 (p : Pattern) : 0 ≤ d1753 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1752 p)
def d1754 (p : Pattern) : Int := if p 182 then d1753 p else d59 p
theorem agree1754 (p q : Pattern) (h : Agree support p q) : d1754 p = d1754 q := by
  simp only [d1754, h 182 (by decide), agree1753 p q h, agree59 p q h]
theorem nonnegative1754 (p : Pattern) : 0 ≤ d1754 p :=
  nonnegative_ite (p 182) (nonnegative1753 p) (nonnegative59 p)
def d1755 (p : Pattern) : Int := if p 163 then d1754 p else d1698 p
theorem agree1755 (p q : Pattern) (h : Agree support p q) : d1755 p = d1755 q := by
  simp only [d1755, h 163 (by decide), agree1754 p q h, agree1698 p q h]
theorem nonnegative1755 (p : Pattern) : 0 ≤ d1755 p :=
  nonnegative_ite (p 163) (nonnegative1754 p) (nonnegative1698 p)
def d1756 (p : Pattern) : Int := if p 182 then d1730 p else d41 p
theorem agree1756 (p q : Pattern) (h : Agree support p q) : d1756 p = d1756 q := by
  simp only [d1756, h 182 (by decide), agree1730 p q h, agree41 p q h]
theorem nonnegative1756 (p : Pattern) : 0 ≤ d1756 p :=
  nonnegative_ite (p 182) (nonnegative1730 p) (nonnegative41 p)
def d1757 (p : Pattern) : Int := if p 163 then d12 p else d1756 p
theorem agree1757 (p q : Pattern) (h : Agree support p q) : d1757 p = d1757 q := by
  simp only [d1757, h 163 (by decide), agree12 p q h, agree1756 p q h]
theorem nonnegative1757 (p : Pattern) : 0 ≤ d1757 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1756 p)
def d1758 (p : Pattern) : Int := if p 162 then d1757 p else d1755 p
theorem agree1758 (p q : Pattern) (h : Agree support p q) : d1758 p = d1758 q := by
  simp only [d1758, h 162 (by decide), agree1757 p q h, agree1755 p q h]
theorem nonnegative1758 (p : Pattern) : 0 ≤ d1758 p :=
  nonnegative_ite (p 162) (nonnegative1757 p) (nonnegative1755 p)
def d1759 (p : Pattern) : Int := if p 161 then d1758 p else d1750 p
theorem agree1759 (p q : Pattern) (h : Agree support p q) : d1759 p = d1759 q := by
  simp only [d1759, h 161 (by decide), agree1758 p q h, agree1750 p q h]
theorem nonnegative1759 (p : Pattern) : 0 ≤ d1759 p :=
  nonnegative_ite (p 161) (nonnegative1758 p) (nonnegative1750 p)
def d1760 (p : Pattern) : Int := if p 182 then d12 p else d32 p
theorem agree1760 (p q : Pattern) (h : Agree support p q) : d1760 p = d1760 q := by
  simp only [d1760, h 182 (by decide), agree12 p q h, agree32 p q h]
theorem nonnegative1760 (p : Pattern) : 0 ≤ d1760 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative32 p)
def d1761 (p : Pattern) : Int := if p 163 then d1760 p else d1726 p
theorem agree1761 (p q : Pattern) (h : Agree support p q) : d1761 p = d1761 q := by
  simp only [d1761, h 163 (by decide), agree1760 p q h, agree1726 p q h]
theorem nonnegative1761 (p : Pattern) : 0 ≤ d1761 p :=
  nonnegative_ite (p 163) (nonnegative1760 p) (nonnegative1726 p)
def d1762 (p : Pattern) : Int := if p 163 then d527 p else d1732 p
theorem agree1762 (p q : Pattern) (h : Agree support p q) : d1762 p = d1762 q := by
  simp only [d1762, h 163 (by decide), agree527 p q h, agree1732 p q h]
theorem nonnegative1762 (p : Pattern) : 0 ≤ d1762 p :=
  nonnegative_ite (p 163) (nonnegative527 p) (nonnegative1732 p)
def d1763 (p : Pattern) : Int := if p 162 then d1762 p else d1761 p
theorem agree1763 (p q : Pattern) (h : Agree support p q) : d1763 p = d1763 q := by
  simp only [d1763, h 162 (by decide), agree1762 p q h, agree1761 p q h]
theorem nonnegative1763 (p : Pattern) : 0 ≤ d1763 p :=
  nonnegative_ite (p 162) (nonnegative1762 p) (nonnegative1761 p)
def d1764 (p : Pattern) : Int := if p 163 then d277 p else d1732 p
theorem agree1764 (p q : Pattern) (h : Agree support p q) : d1764 p = d1764 q := by
  simp only [d1764, h 163 (by decide), agree277 p q h, agree1732 p q h]
theorem nonnegative1764 (p : Pattern) : 0 ≤ d1764 p :=
  nonnegative_ite (p 163) (nonnegative277 p) (nonnegative1732 p)
def d1765 (p : Pattern) : Int := if p 162 then d539 p else d1764 p
theorem agree1765 (p q : Pattern) (h : Agree support p q) : d1765 p = d1765 q := by
  simp only [d1765, h 162 (by decide), agree539 p q h, agree1764 p q h]
theorem nonnegative1765 (p : Pattern) : 0 ≤ d1765 p :=
  nonnegative_ite (p 162) (nonnegative539 p) (nonnegative1764 p)
def d1766 (p : Pattern) : Int := if p 161 then d1765 p else d1763 p
theorem agree1766 (p q : Pattern) (h : Agree support p q) : d1766 p = d1766 q := by
  simp only [d1766, h 161 (by decide), agree1765 p q h, agree1763 p q h]
theorem nonnegative1766 (p : Pattern) : 0 ≤ d1766 p :=
  nonnegative_ite (p 161) (nonnegative1765 p) (nonnegative1763 p)
def d1767 (p : Pattern) : Int := if p 160 then d1766 p else d1759 p
theorem agree1767 (p q : Pattern) (h : Agree support p q) : d1767 p = d1767 q := by
  simp only [d1767, h 160 (by decide), agree1766 p q h, agree1759 p q h]
theorem nonnegative1767 (p : Pattern) : 0 ≤ d1767 p :=
  nonnegative_ite (p 160) (nonnegative1766 p) (nonnegative1759 p)
def d1768 (p : Pattern) : Int := if p 141 then d1767 p else d1739 p
theorem agree1768 (p q : Pattern) (h : Agree support p q) : d1768 p = d1768 q := by
  simp only [d1768, h 141 (by decide), agree1767 p q h, agree1739 p q h]
theorem nonnegative1768 (p : Pattern) : 0 ≤ d1768 p :=
  nonnegative_ite (p 141) (nonnegative1767 p) (nonnegative1739 p)
def d1769 (p : Pattern) : Int := if p 247 then d4 p else d0 p
theorem agree1769 (p q : Pattern) (h : Agree support p q) : d1769 p = d1769 q := by
  simp only [d1769, h 247 (by decide), agree4 p q h, agree0 p q h]
theorem nonnegative1769 (p : Pattern) : 0 ≤ d1769 p :=
  nonnegative_ite (p 247) (nonnegative4 p) (nonnegative0 p)
def d1770 (p : Pattern) : Int := if p 246 then d17 p else d1769 p
theorem agree1770 (p q : Pattern) (h : Agree support p q) : d1770 p = d1770 q := by
  simp only [d1770, h 246 (by decide), agree17 p q h, agree1769 p q h]
theorem nonnegative1770 (p : Pattern) : 0 ≤ d1770 p :=
  nonnegative_ite (p 246) (nonnegative17 p) (nonnegative1769 p)
def d1771 (p : Pattern) : Int := if p 225 then d1770 p else d14 p
theorem agree1771 (p q : Pattern) (h : Agree support p q) : d1771 p = d1771 q := by
  simp only [d1771, h 225 (by decide), agree1770 p q h, agree14 p q h]
theorem nonnegative1771 (p : Pattern) : 0 ≤ d1771 p :=
  nonnegative_ite (p 225) (nonnegative1770 p) (nonnegative14 p)
def d1772 (p : Pattern) : Int := if p 224 then d1770 p else d1771 p
theorem agree1772 (p q : Pattern) (h : Agree support p q) : d1772 p = d1772 q := by
  simp only [d1772, h 224 (by decide), agree1770 p q h, agree1771 p q h]
theorem nonnegative1772 (p : Pattern) : 0 ≤ d1772 p :=
  nonnegative_ite (p 224) (nonnegative1770 p) (nonnegative1771 p)
def d1773 (p : Pattern) : Int := if p 204 then d12 p else d1772 p
theorem agree1773 (p q : Pattern) (h : Agree support p q) : d1773 p = d1773 q := by
  simp only [d1773, h 204 (by decide), agree12 p q h, agree1772 p q h]
theorem nonnegative1773 (p : Pattern) : 0 ≤ d1773 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1772 p)
def d1774 (p : Pattern) : Int := if p 182 then d1773 p else d15 p
theorem agree1774 (p q : Pattern) (h : Agree support p q) : d1774 p = d1774 q := by
  simp only [d1774, h 182 (by decide), agree1773 p q h, agree15 p q h]
theorem nonnegative1774 (p : Pattern) : 0 ≤ d1774 p :=
  nonnegative_ite (p 182) (nonnegative1773 p) (nonnegative15 p)
def d1775 (p : Pattern) : Int := if p 247 then d6 p else d0 p
theorem agree1775 (p q : Pattern) (h : Agree support p q) : d1775 p = d1775 q := by
  simp only [d1775, h 247 (by decide), agree6 p q h, agree0 p q h]
theorem nonnegative1775 (p : Pattern) : 0 ≤ d1775 p :=
  nonnegative_ite (p 247) (nonnegative6 p) (nonnegative0 p)
def d1776 (p : Pattern) : Int := if p 246 then d34 p else d1775 p
theorem agree1776 (p q : Pattern) (h : Agree support p q) : d1776 p = d1776 q := by
  simp only [d1776, h 246 (by decide), agree34 p q h, agree1775 p q h]
theorem nonnegative1776 (p : Pattern) : 0 ≤ d1776 p :=
  nonnegative_ite (p 246) (nonnegative34 p) (nonnegative1775 p)
def d1777 (p : Pattern) : Int := if p 225 then d1776 p else d14 p
theorem agree1777 (p q : Pattern) (h : Agree support p q) : d1777 p = d1777 q := by
  simp only [d1777, h 225 (by decide), agree1776 p q h, agree14 p q h]
theorem nonnegative1777 (p : Pattern) : 0 ≤ d1777 p :=
  nonnegative_ite (p 225) (nonnegative1776 p) (nonnegative14 p)
def d1778 (p : Pattern) : Int := if p 247 then d8 p else d0 p
theorem agree1778 (p q : Pattern) (h : Agree support p q) : d1778 p = d1778 q := by
  simp only [d1778, h 247 (by decide), agree8 p q h, agree0 p q h]
theorem nonnegative1778 (p : Pattern) : 0 ≤ d1778 p :=
  nonnegative_ite (p 247) (nonnegative8 p) (nonnegative0 p)
def d1779 (p : Pattern) : Int := if p 246 then d190 p else d1778 p
theorem agree1779 (p q : Pattern) (h : Agree support p q) : d1779 p = d1779 q := by
  simp only [d1779, h 246 (by decide), agree190 p q h, agree1778 p q h]
theorem nonnegative1779 (p : Pattern) : 0 ≤ d1779 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative1778 p)
def d1780 (p : Pattern) : Int := if p 225 then d1779 p else d1770 p
theorem agree1780 (p q : Pattern) (h : Agree support p q) : d1780 p = d1780 q := by
  simp only [d1780, h 225 (by decide), agree1779 p q h, agree1770 p q h]
theorem nonnegative1780 (p : Pattern) : 0 ≤ d1780 p :=
  nonnegative_ite (p 225) (nonnegative1779 p) (nonnegative1770 p)
def d1781 (p : Pattern) : Int := if p 224 then d1780 p else d1777 p
theorem agree1781 (p q : Pattern) (h : Agree support p q) : d1781 p = d1781 q := by
  simp only [d1781, h 224 (by decide), agree1780 p q h, agree1777 p q h]
theorem nonnegative1781 (p : Pattern) : 0 ≤ d1781 p :=
  nonnegative_ite (p 224) (nonnegative1780 p) (nonnegative1777 p)
def d1782 (p : Pattern) : Int := if p 204 then d12 p else d1781 p
theorem agree1782 (p q : Pattern) (h : Agree support p q) : d1782 p = d1782 q := by
  simp only [d1782, h 204 (by decide), agree12 p q h, agree1781 p q h]
theorem nonnegative1782 (p : Pattern) : 0 ≤ d1782 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1781 p)
def d1783 (p : Pattern) : Int := if p 182 then d1782 p else d15 p
theorem agree1783 (p q : Pattern) (h : Agree support p q) : d1783 p = d1783 q := by
  simp only [d1783, h 182 (by decide), agree1782 p q h, agree15 p q h]
theorem nonnegative1783 (p : Pattern) : 0 ≤ d1783 p :=
  nonnegative_ite (p 182) (nonnegative1782 p) (nonnegative15 p)
def d1784 (p : Pattern) : Int := if p 163 then d1783 p else d1774 p
theorem agree1784 (p q : Pattern) (h : Agree support p q) : d1784 p = d1784 q := by
  simp only [d1784, h 163 (by decide), agree1783 p q h, agree1774 p q h]
theorem nonnegative1784 (p : Pattern) : 0 ≤ d1784 p :=
  nonnegative_ite (p 163) (nonnegative1783 p) (nonnegative1774 p)
def d1785 (p : Pattern) : Int := if p 247 then d11 p else d0 p
theorem agree1785 (p q : Pattern) (h : Agree support p q) : d1785 p = d1785 q := by
  simp only [d1785, h 247 (by decide), agree11 p q h, agree0 p q h]
theorem nonnegative1785 (p : Pattern) : 0 ≤ d1785 p :=
  nonnegative_ite (p 247) (nonnegative11 p) (nonnegative0 p)
def d1786 (p : Pattern) : Int := if p 246 then d23 p else d1785 p
theorem agree1786 (p q : Pattern) (h : Agree support p q) : d1786 p = d1786 q := by
  simp only [d1786, h 246 (by decide), agree23 p q h, agree1785 p q h]
theorem nonnegative1786 (p : Pattern) : 0 ≤ d1786 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative1785 p)
def d1787 (p : Pattern) : Int := if p 225 then d1786 p else d1770 p
theorem agree1787 (p q : Pattern) (h : Agree support p q) : d1787 p = d1787 q := by
  simp only [d1787, h 225 (by decide), agree1786 p q h, agree1770 p q h]
theorem nonnegative1787 (p : Pattern) : 0 ≤ d1787 p :=
  nonnegative_ite (p 225) (nonnegative1786 p) (nonnegative1770 p)
def d1788 (p : Pattern) : Int := if p 224 then d1787 p else d1777 p
theorem agree1788 (p q : Pattern) (h : Agree support p q) : d1788 p = d1788 q := by
  simp only [d1788, h 224 (by decide), agree1787 p q h, agree1777 p q h]
theorem nonnegative1788 (p : Pattern) : 0 ≤ d1788 p :=
  nonnegative_ite (p 224) (nonnegative1787 p) (nonnegative1777 p)
def d1789 (p : Pattern) : Int := if p 204 then d12 p else d1788 p
theorem agree1789 (p q : Pattern) (h : Agree support p q) : d1789 p = d1789 q := by
  simp only [d1789, h 204 (by decide), agree12 p q h, agree1788 p q h]
theorem nonnegative1789 (p : Pattern) : 0 ≤ d1789 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1788 p)
def d1790 (p : Pattern) : Int := if p 182 then d1789 p else d15 p
theorem agree1790 (p q : Pattern) (h : Agree support p q) : d1790 p = d1790 q := by
  simp only [d1790, h 182 (by decide), agree1789 p q h, agree15 p q h]
theorem nonnegative1790 (p : Pattern) : 0 ≤ d1790 p :=
  nonnegative_ite (p 182) (nonnegative1789 p) (nonnegative15 p)
def d1791 (p : Pattern) : Int := if p 247 then d10 p else d4 p
theorem agree1791 (p q : Pattern) (h : Agree support p q) : d1791 p = d1791 q := by
  simp only [d1791, h 247 (by decide), agree10 p q h, agree4 p q h]
theorem nonnegative1791 (p : Pattern) : 0 ≤ d1791 p :=
  nonnegative_ite (p 247) (nonnegative10 p) (nonnegative4 p)
def d1792 (p : Pattern) : Int := if p 246 then d57 p else d1791 p
theorem agree1792 (p q : Pattern) (h : Agree support p q) : d1792 p = d1792 q := by
  simp only [d1792, h 246 (by decide), agree57 p q h, agree1791 p q h]
theorem nonnegative1792 (p : Pattern) : 0 ≤ d1792 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative1791 p)
def d1793 (p : Pattern) : Int := if p 225 then d1792 p else d18 p
theorem agree1793 (p q : Pattern) (h : Agree support p q) : d1793 p = d1793 q := by
  simp only [d1793, h 225 (by decide), agree1792 p q h, agree18 p q h]
theorem nonnegative1793 (p : Pattern) : 0 ≤ d1793 p :=
  nonnegative_ite (p 225) (nonnegative1792 p) (nonnegative18 p)
def d1794 (p : Pattern) : Int := if p 247 then d8 p else d4 p
theorem agree1794 (p q : Pattern) (h : Agree support p q) : d1794 p = d1794 q := by
  simp only [d1794, h 247 (by decide), agree8 p q h, agree4 p q h]
theorem nonnegative1794 (p : Pattern) : 0 ≤ d1794 p :=
  nonnegative_ite (p 247) (nonnegative8 p) (nonnegative4 p)
def d1795 (p : Pattern) : Int := if p 246 then d190 p else d1794 p
theorem agree1795 (p q : Pattern) (h : Agree support p q) : d1795 p = d1795 q := by
  simp only [d1795, h 246 (by decide), agree190 p q h, agree1794 p q h]
theorem nonnegative1795 (p : Pattern) : 0 ≤ d1795 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative1794 p)
def d1796 (p : Pattern) : Int := if p 225 then d339 p else d1795 p
theorem agree1796 (p q : Pattern) (h : Agree support p q) : d1796 p = d1796 q := by
  simp only [d1796, h 225 (by decide), agree339 p q h, agree1795 p q h]
theorem nonnegative1796 (p : Pattern) : 0 ≤ d1796 p :=
  nonnegative_ite (p 225) (nonnegative339 p) (nonnegative1795 p)
def d1797 (p : Pattern) : Int := if p 224 then d1796 p else d1793 p
theorem agree1797 (p q : Pattern) (h : Agree support p q) : d1797 p = d1797 q := by
  simp only [d1797, h 224 (by decide), agree1796 p q h, agree1793 p q h]
theorem nonnegative1797 (p : Pattern) : 0 ≤ d1797 p :=
  nonnegative_ite (p 224) (nonnegative1796 p) (nonnegative1793 p)
def d1798 (p : Pattern) : Int := if p 204 then d12 p else d1797 p
theorem agree1798 (p q : Pattern) (h : Agree support p q) : d1798 p = d1798 q := by
  simp only [d1798, h 204 (by decide), agree12 p q h, agree1797 p q h]
theorem nonnegative1798 (p : Pattern) : 0 ≤ d1798 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1797 p)
def d1799 (p : Pattern) : Int := if p 182 then d1798 p else d19 p
theorem agree1799 (p q : Pattern) (h : Agree support p q) : d1799 p = d1799 q := by
  simp only [d1799, h 182 (by decide), agree1798 p q h, agree19 p q h]
theorem nonnegative1799 (p : Pattern) : 0 ≤ d1799 p :=
  nonnegative_ite (p 182) (nonnegative1798 p) (nonnegative19 p)
end NetHack.Sokoban22Refined85
