/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5880 (p : Pattern) : Int := if p 163 then d12 p else d1803 p
theorem agree5880 (p q : Pattern) (h : Agree support p q) : d5880 p = d5880 q := by
  simp only [d5880, h 163 (by decide), agree12 p q h, agree1803 p q h]
theorem nonnegative5880 (p : Pattern) : 0 ≤ d5880 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1803 p)
def d5881 (p : Pattern) : Int := if p 162 then d5880 p else d5878 p
theorem agree5881 (p q : Pattern) (h : Agree support p q) : d5881 p = d5881 q := by
  simp only [d5881, h 162 (by decide), agree5880 p q h, agree5878 p q h]
theorem nonnegative5881 (p : Pattern) : 0 ≤ d5881 p :=
  nonnegative_ite (p 162) (nonnegative5880 p) (nonnegative5878 p)
def d5882 (p : Pattern) : Int := if p 161 then d5881 p else d5879 p
theorem agree5882 (p q : Pattern) (h : Agree support p q) : d5882 p = d5882 q := by
  simp only [d5882, h 161 (by decide), agree5881 p q h, agree5879 p q h]
theorem nonnegative5882 (p : Pattern) : 0 ≤ d5882 p :=
  nonnegative_ite (p 161) (nonnegative5881 p) (nonnegative5879 p)
def d5883 (p : Pattern) : Int := if p 160 then d5864 p else d5882 p
theorem agree5883 (p q : Pattern) (h : Agree support p q) : d5883 p = d5883 q := by
  simp only [d5883, h 160 (by decide), agree5864 p q h, agree5882 p q h]
theorem nonnegative5883 (p : Pattern) : 0 ≤ d5883 p :=
  nonnegative_ite (p 160) (nonnegative5864 p) (nonnegative5882 p)
def d5884 (p : Pattern) : Int := if p 163 then d1717 p else d1781 p
theorem agree5884 (p q : Pattern) (h : Agree support p q) : d5884 p = d5884 q := by
  simp only [d5884, h 163 (by decide), agree1717 p q h, agree1781 p q h]
theorem nonnegative5884 (p : Pattern) : 0 ≤ d5884 p :=
  nonnegative_ite (p 163) (nonnegative1717 p) (nonnegative1781 p)
def d5885 (p : Pattern) : Int := if p 163 then d1803 p else d1797 p
theorem agree5885 (p q : Pattern) (h : Agree support p q) : d5885 p = d5885 q := by
  simp only [d5885, h 163 (by decide), agree1803 p q h, agree1797 p q h]
theorem nonnegative5885 (p : Pattern) : 0 ≤ d5885 p :=
  nonnegative_ite (p 163) (nonnegative1803 p) (nonnegative1797 p)
def d5886 (p : Pattern) : Int := if p 162 then d5885 p else d5884 p
theorem agree5886 (p q : Pattern) (h : Agree support p q) : d5886 p = d5886 q := by
  simp only [d5886, h 162 (by decide), agree5885 p q h, agree5884 p q h]
theorem nonnegative5886 (p : Pattern) : 0 ≤ d5886 p :=
  nonnegative_ite (p 162) (nonnegative5885 p) (nonnegative5884 p)
def d5887 (p : Pattern) : Int := if p 163 then d1752 p else d1797 p
theorem agree5887 (p q : Pattern) (h : Agree support p q) : d5887 p = d5887 q := by
  simp only [d5887, h 163 (by decide), agree1752 p q h, agree1797 p q h]
theorem nonnegative5887 (p : Pattern) : 0 ≤ d5887 p :=
  nonnegative_ite (p 163) (nonnegative1752 p) (nonnegative1797 p)
def d5888 (p : Pattern) : Int := if p 162 then d5862 p else d5887 p
theorem agree5888 (p q : Pattern) (h : Agree support p q) : d5888 p = d5888 q := by
  simp only [d5888, h 162 (by decide), agree5862 p q h, agree5887 p q h]
theorem nonnegative5888 (p : Pattern) : 0 ≤ d5888 p :=
  nonnegative_ite (p 162) (nonnegative5862 p) (nonnegative5887 p)
def d5889 (p : Pattern) : Int := if p 161 then d5888 p else d5886 p
theorem agree5889 (p q : Pattern) (h : Agree support p q) : d5889 p = d5889 q := by
  simp only [d5889, h 161 (by decide), agree5888 p q h, agree5886 p q h]
theorem nonnegative5889 (p : Pattern) : 0 ≤ d5889 p :=
  nonnegative_ite (p 161) (nonnegative5888 p) (nonnegative5886 p)
def d5890 (p : Pattern) : Int := if p 160 then d5874 p else d5889 p
theorem agree5890 (p q : Pattern) (h : Agree support p q) : d5890 p = d5890 q := by
  simp only [d5890, h 160 (by decide), agree5874 p q h, agree5889 p q h]
theorem nonnegative5890 (p : Pattern) : 0 ≤ d5890 p :=
  nonnegative_ite (p 160) (nonnegative5874 p) (nonnegative5889 p)
def d5891 (p : Pattern) : Int := if p 141 then d5890 p else d5883 p
theorem agree5891 (p q : Pattern) (h : Agree support p q) : d5891 p = d5891 q := by
  simp only [d5891, h 141 (by decide), agree5890 p q h, agree5883 p q h]
theorem nonnegative5891 (p : Pattern) : 0 ≤ d5891 p :=
  nonnegative_ite (p 141) (nonnegative5890 p) (nonnegative5883 p)
def d5892 (p : Pattern) : Int := if p 138 then d5891 p else d5876 p
theorem agree5892 (p q : Pattern) (h : Agree support p q) : d5892 p = d5892 q := by
  simp only [d5892, h 138 (by decide), agree5891 p q h, agree5876 p q h]
theorem nonnegative5892 (p : Pattern) : 0 ≤ d5892 p :=
  nonnegative_ite (p 138) (nonnegative5891 p) (nonnegative5876 p)
def d5893 (p : Pattern) : Int := if p 163 then d1729 p else d1803 p
theorem agree5893 (p q : Pattern) (h : Agree support p q) : d5893 p = d5893 q := by
  simp only [d5893, h 163 (by decide), agree1729 p q h, agree1803 p q h]
theorem nonnegative5893 (p : Pattern) : 0 ≤ d5893 p :=
  nonnegative_ite (p 163) (nonnegative1729 p) (nonnegative1803 p)
def d5894 (p : Pattern) : Int := if p 162 then d5862 p else d5893 p
theorem agree5894 (p q : Pattern) (h : Agree support p q) : d5894 p = d5894 q := by
  simp only [d5894, h 162 (by decide), agree5862 p q h, agree5893 p q h]
theorem nonnegative5894 (p : Pattern) : 0 ≤ d5894 p :=
  nonnegative_ite (p 162) (nonnegative5862 p) (nonnegative5893 p)
def d5895 (p : Pattern) : Int := if p 162 then d12 p else d5862 p
theorem agree5895 (p q : Pattern) (h : Agree support p q) : d5895 p = d5895 q := by
  simp only [d5895, h 162 (by decide), agree12 p q h, agree5862 p q h]
theorem nonnegative5895 (p : Pattern) : 0 ≤ d5895 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5862 p)
def d5896 (p : Pattern) : Int := if p 161 then d5895 p else d5894 p
theorem agree5896 (p q : Pattern) (h : Agree support p q) : d5896 p = d5896 q := by
  simp only [d5896, h 161 (by decide), agree5895 p q h, agree5894 p q h]
theorem nonnegative5896 (p : Pattern) : 0 ≤ d5896 p :=
  nonnegative_ite (p 161) (nonnegative5895 p) (nonnegative5894 p)
def d5897 (p : Pattern) : Int := if p 161 then d12 p else d5895 p
theorem agree5897 (p q : Pattern) (h : Agree support p q) : d5897 p = d5897 q := by
  simp only [d5897, h 161 (by decide), agree12 p q h, agree5895 p q h]
theorem nonnegative5897 (p : Pattern) : 0 ≤ d5897 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5895 p)
def d5898 (p : Pattern) : Int := if p 160 then d5897 p else d5896 p
theorem agree5898 (p q : Pattern) (h : Agree support p q) : d5898 p = d5898 q := by
  simp only [d5898, h 160 (by decide), agree5897 p q h, agree5896 p q h]
theorem nonnegative5898 (p : Pattern) : 0 ≤ d5898 p :=
  nonnegative_ite (p 160) (nonnegative5897 p) (nonnegative5896 p)
def d5899 (p : Pattern) : Int := if p 160 then d12 p else d5897 p
theorem agree5899 (p q : Pattern) (h : Agree support p q) : d5899 p = d5899 q := by
  simp only [d5899, h 160 (by decide), agree12 p q h, agree5897 p q h]
theorem nonnegative5899 (p : Pattern) : 0 ≤ d5899 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5897 p)
def d5900 (p : Pattern) : Int := if p 141 then d5899 p else d5898 p
theorem agree5900 (p q : Pattern) (h : Agree support p q) : d5900 p = d5900 q := by
  simp only [d5900, h 141 (by decide), agree5899 p q h, agree5898 p q h]
theorem nonnegative5900 (p : Pattern) : 0 ≤ d5900 p :=
  nonnegative_ite (p 141) (nonnegative5899 p) (nonnegative5898 p)
def d5901 (p : Pattern) : Int := if p 138 then d5900 p else d5891 p
theorem agree5901 (p q : Pattern) (h : Agree support p q) : d5901 p = d5901 q := by
  simp only [d5901, h 138 (by decide), agree5900 p q h, agree5891 p q h]
theorem nonnegative5901 (p : Pattern) : 0 ≤ d5901 p :=
  nonnegative_ite (p 138) (nonnegative5900 p) (nonnegative5891 p)
def d5902 (p : Pattern) : Int := if p 116 then d5901 p else d5892 p
theorem agree5902 (p q : Pattern) (h : Agree support p q) : d5902 p = d5902 q := by
  simp only [d5902, h 116 (by decide), agree5901 p q h, agree5892 p q h]
theorem nonnegative5902 (p : Pattern) : 0 ≤ d5902 p :=
  nonnegative_ite (p 116) (nonnegative5901 p) (nonnegative5892 p)
def d5903 (p : Pattern) : Int := if p 138 then d12 p else d5891 p
theorem agree5903 (p q : Pattern) (h : Agree support p q) : d5903 p = d5903 q := by
  simp only [d5903, h 138 (by decide), agree12 p q h, agree5891 p q h]
theorem nonnegative5903 (p : Pattern) : 0 ≤ d5903 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5891 p)
def d5904 (p : Pattern) : Int := if p 116 then d5903 p else d5892 p
theorem agree5904 (p q : Pattern) (h : Agree support p q) : d5904 p = d5904 q := by
  simp only [d5904, h 116 (by decide), agree5903 p q h, agree5892 p q h]
theorem nonnegative5904 (p : Pattern) : 0 ≤ d5904 p :=
  nonnegative_ite (p 116) (nonnegative5903 p) (nonnegative5892 p)
def d5905 (p : Pattern) : Int := if p 115 then d5904 p else d5902 p
theorem agree5905 (p q : Pattern) (h : Agree support p q) : d5905 p = d5905 q := by
  simp only [d5905, h 115 (by decide), agree5904 p q h, agree5902 p q h]
theorem nonnegative5905 (p : Pattern) : 0 ≤ d5905 p :=
  nonnegative_ite (p 115) (nonnegative5904 p) (nonnegative5902 p)
def d5906 (p : Pattern) : Int := if p 163 then d1883 p else d1875 p
theorem agree5906 (p q : Pattern) (h : Agree support p q) : d5906 p = d5906 q := by
  simp only [d5906, h 163 (by decide), agree1883 p q h, agree1875 p q h]
theorem nonnegative5906 (p : Pattern) : 0 ≤ d5906 p :=
  nonnegative_ite (p 163) (nonnegative1883 p) (nonnegative1875 p)
def d5907 (p : Pattern) : Int := if p 162 then d5906 p else d1875 p
theorem agree5907 (p q : Pattern) (h : Agree support p q) : d5907 p = d5907 q := by
  simp only [d5907, h 162 (by decide), agree5906 p q h, agree1875 p q h]
theorem nonnegative5907 (p : Pattern) : 0 ≤ d5907 p :=
  nonnegative_ite (p 162) (nonnegative5906 p) (nonnegative1875 p)
def d5908 (p : Pattern) : Int := if p 163 then d12 p else d1752 p
theorem agree5908 (p q : Pattern) (h : Agree support p q) : d5908 p = d5908 q := by
  simp only [d5908, h 163 (by decide), agree12 p q h, agree1752 p q h]
theorem nonnegative5908 (p : Pattern) : 0 ≤ d5908 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1752 p)
def d5909 (p : Pattern) : Int := if p 162 then d5908 p else d5906 p
theorem agree5909 (p q : Pattern) (h : Agree support p q) : d5909 p = d5909 q := by
  simp only [d5909, h 162 (by decide), agree5908 p q h, agree5906 p q h]
theorem nonnegative5909 (p : Pattern) : 0 ≤ d5909 p :=
  nonnegative_ite (p 162) (nonnegative5908 p) (nonnegative5906 p)
def d5910 (p : Pattern) : Int := if p 161 then d5909 p else d5907 p
theorem agree5910 (p q : Pattern) (h : Agree support p q) : d5910 p = d5910 q := by
  simp only [d5910, h 161 (by decide), agree5909 p q h, agree5907 p q h]
theorem nonnegative5910 (p : Pattern) : 0 ≤ d5910 p :=
  nonnegative_ite (p 161) (nonnegative5909 p) (nonnegative5907 p)
def d5911 (p : Pattern) : Int := if p 163 then d1905 p else d1898 p
theorem agree5911 (p q : Pattern) (h : Agree support p q) : d5911 p = d5911 q := by
  simp only [d5911, h 163 (by decide), agree1905 p q h, agree1898 p q h]
theorem nonnegative5911 (p : Pattern) : 0 ≤ d5911 p :=
  nonnegative_ite (p 163) (nonnegative1905 p) (nonnegative1898 p)
def d5912 (p : Pattern) : Int := if p 162 then d12 p else d5911 p
theorem agree5912 (p q : Pattern) (h : Agree support p q) : d5912 p = d5912 q := by
  simp only [d5912, h 162 (by decide), agree12 p q h, agree5911 p q h]
theorem nonnegative5912 (p : Pattern) : 0 ≤ d5912 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5911 p)
def d5913 (p : Pattern) : Int := if p 161 then d12 p else d5912 p
theorem agree5913 (p q : Pattern) (h : Agree support p q) : d5913 p = d5913 q := by
  simp only [d5913, h 161 (by decide), agree12 p q h, agree5912 p q h]
theorem nonnegative5913 (p : Pattern) : 0 ≤ d5913 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5912 p)
def d5914 (p : Pattern) : Int := if p 160 then d5913 p else d5910 p
theorem agree5914 (p q : Pattern) (h : Agree support p q) : d5914 p = d5914 q := by
  simp only [d5914, h 160 (by decide), agree5913 p q h, agree5910 p q h]
theorem nonnegative5914 (p : Pattern) : 0 ≤ d5914 p :=
  nonnegative_ite (p 160) (nonnegative5913 p) (nonnegative5910 p)
def d5915 (p : Pattern) : Int := if p 163 then d1921 p else d1875 p
theorem agree5915 (p q : Pattern) (h : Agree support p q) : d5915 p = d5915 q := by
  simp only [d5915, h 163 (by decide), agree1921 p q h, agree1875 p q h]
theorem nonnegative5915 (p : Pattern) : 0 ≤ d5915 p :=
  nonnegative_ite (p 163) (nonnegative1921 p) (nonnegative1875 p)
def d5916 (p : Pattern) : Int := if p 163 then d1752 p else d1883 p
theorem agree5916 (p q : Pattern) (h : Agree support p q) : d5916 p = d5916 q := by
  simp only [d5916, h 163 (by decide), agree1752 p q h, agree1883 p q h]
theorem nonnegative5916 (p : Pattern) : 0 ≤ d5916 p :=
  nonnegative_ite (p 163) (nonnegative1752 p) (nonnegative1883 p)
def d5917 (p : Pattern) : Int := if p 162 then d5916 p else d5915 p
theorem agree5917 (p q : Pattern) (h : Agree support p q) : d5917 p = d5917 q := by
  simp only [d5917, h 162 (by decide), agree5916 p q h, agree5915 p q h]
theorem nonnegative5917 (p : Pattern) : 0 ≤ d5917 p :=
  nonnegative_ite (p 162) (nonnegative5916 p) (nonnegative5915 p)
def d5918 (p : Pattern) : Int := if p 163 then d1729 p else d1883 p
theorem agree5918 (p q : Pattern) (h : Agree support p q) : d5918 p = d5918 q := by
  simp only [d5918, h 163 (by decide), agree1729 p q h, agree1883 p q h]
theorem nonnegative5918 (p : Pattern) : 0 ≤ d5918 p :=
  nonnegative_ite (p 163) (nonnegative1729 p) (nonnegative1883 p)
def d5919 (p : Pattern) : Int := if p 162 then d12 p else d5918 p
theorem agree5919 (p q : Pattern) (h : Agree support p q) : d5919 p = d5919 q := by
  simp only [d5919, h 162 (by decide), agree12 p q h, agree5918 p q h]
theorem nonnegative5919 (p : Pattern) : 0 ≤ d5919 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5918 p)
def d5920 (p : Pattern) : Int := if p 161 then d5919 p else d5917 p
theorem agree5920 (p q : Pattern) (h : Agree support p q) : d5920 p = d5920 q := by
  simp only [d5920, h 161 (by decide), agree5919 p q h, agree5917 p q h]
theorem nonnegative5920 (p : Pattern) : 0 ≤ d5920 p :=
  nonnegative_ite (p 161) (nonnegative5919 p) (nonnegative5917 p)
def d5921 (p : Pattern) : Int := if p 163 then d12 p else d1905 p
theorem agree5921 (p q : Pattern) (h : Agree support p q) : d5921 p = d5921 q := by
  simp only [d5921, h 163 (by decide), agree12 p q h, agree1905 p q h]
theorem nonnegative5921 (p : Pattern) : 0 ≤ d5921 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1905 p)
def d5922 (p : Pattern) : Int := if p 162 then d12 p else d5921 p
theorem agree5922 (p q : Pattern) (h : Agree support p q) : d5922 p = d5922 q := by
  simp only [d5922, h 162 (by decide), agree12 p q h, agree5921 p q h]
theorem nonnegative5922 (p : Pattern) : 0 ≤ d5922 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5921 p)
def d5923 (p : Pattern) : Int := if p 161 then d12 p else d5922 p
theorem agree5923 (p q : Pattern) (h : Agree support p q) : d5923 p = d5923 q := by
  simp only [d5923, h 161 (by decide), agree12 p q h, agree5922 p q h]
theorem nonnegative5923 (p : Pattern) : 0 ≤ d5923 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5922 p)
def d5924 (p : Pattern) : Int := if p 160 then d5923 p else d5920 p
theorem agree5924 (p q : Pattern) (h : Agree support p q) : d5924 p = d5924 q := by
  simp only [d5924, h 160 (by decide), agree5923 p q h, agree5920 p q h]
theorem nonnegative5924 (p : Pattern) : 0 ≤ d5924 p :=
  nonnegative_ite (p 160) (nonnegative5923 p) (nonnegative5920 p)
def d5925 (p : Pattern) : Int := if p 141 then d5924 p else d5914 p
theorem agree5925 (p q : Pattern) (h : Agree support p q) : d5925 p = d5925 q := by
  simp only [d5925, h 141 (by decide), agree5924 p q h, agree5914 p q h]
theorem nonnegative5925 (p : Pattern) : 0 ≤ d5925 p :=
  nonnegative_ite (p 141) (nonnegative5924 p) (nonnegative5914 p)
def d5926 (p : Pattern) : Int := if p 163 then d1951 p else d1942 p
theorem agree5926 (p q : Pattern) (h : Agree support p q) : d5926 p = d5926 q := by
  simp only [d5926, h 163 (by decide), agree1951 p q h, agree1942 p q h]
theorem nonnegative5926 (p : Pattern) : 0 ≤ d5926 p :=
  nonnegative_ite (p 163) (nonnegative1951 p) (nonnegative1942 p)
def d5927 (p : Pattern) : Int := if p 163 then d1966 p else d1957 p
theorem agree5927 (p q : Pattern) (h : Agree support p q) : d5927 p = d5927 q := by
  simp only [d5927, h 163 (by decide), agree1966 p q h, agree1957 p q h]
theorem nonnegative5927 (p : Pattern) : 0 ≤ d5927 p :=
  nonnegative_ite (p 163) (nonnegative1966 p) (nonnegative1957 p)
def d5928 (p : Pattern) : Int := if p 162 then d5927 p else d5926 p
theorem agree5928 (p q : Pattern) (h : Agree support p q) : d5928 p = d5928 q := by
  simp only [d5928, h 162 (by decide), agree5927 p q h, agree5926 p q h]
theorem nonnegative5928 (p : Pattern) : 0 ≤ d5928 p :=
  nonnegative_ite (p 162) (nonnegative5927 p) (nonnegative5926 p)
def d5929 (p : Pattern) : Int := if p 162 then d5908 p else d5927 p
theorem agree5929 (p q : Pattern) (h : Agree support p q) : d5929 p = d5929 q := by
  simp only [d5929, h 162 (by decide), agree5908 p q h, agree5927 p q h]
theorem nonnegative5929 (p : Pattern) : 0 ≤ d5929 p :=
  nonnegative_ite (p 162) (nonnegative5908 p) (nonnegative5927 p)
def d5930 (p : Pattern) : Int := if p 161 then d5929 p else d5928 p
theorem agree5930 (p q : Pattern) (h : Agree support p q) : d5930 p = d5930 q := by
  simp only [d5930, h 161 (by decide), agree5929 p q h, agree5928 p q h]
theorem nonnegative5930 (p : Pattern) : 0 ≤ d5930 p :=
  nonnegative_ite (p 161) (nonnegative5929 p) (nonnegative5928 p)
def d5931 (p : Pattern) : Int := if p 160 then d5913 p else d5930 p
theorem agree5931 (p q : Pattern) (h : Agree support p q) : d5931 p = d5931 q := by
  simp only [d5931, h 160 (by decide), agree5913 p q h, agree5930 p q h]
theorem nonnegative5931 (p : Pattern) : 0 ≤ d5931 p :=
  nonnegative_ite (p 160) (nonnegative5913 p) (nonnegative5930 p)
def d5932 (p : Pattern) : Int := if p 163 then d1898 p else d1951 p
theorem agree5932 (p q : Pattern) (h : Agree support p q) : d5932 p = d5932 q := by
  simp only [d5932, h 163 (by decide), agree1898 p q h, agree1951 p q h]
theorem nonnegative5932 (p : Pattern) : 0 ≤ d5932 p :=
  nonnegative_ite (p 163) (nonnegative1898 p) (nonnegative1951 p)
def d5933 (p : Pattern) : Int := if p 163 then d1752 p else d1966 p
theorem agree5933 (p q : Pattern) (h : Agree support p q) : d5933 p = d5933 q := by
  simp only [d5933, h 163 (by decide), agree1752 p q h, agree1966 p q h]
theorem nonnegative5933 (p : Pattern) : 0 ≤ d5933 p :=
  nonnegative_ite (p 163) (nonnegative1752 p) (nonnegative1966 p)
def d5934 (p : Pattern) : Int := if p 162 then d5933 p else d5932 p
theorem agree5934 (p q : Pattern) (h : Agree support p q) : d5934 p = d5934 q := by
  simp only [d5934, h 162 (by decide), agree5933 p q h, agree5932 p q h]
theorem nonnegative5934 (p : Pattern) : 0 ≤ d5934 p :=
  nonnegative_ite (p 162) (nonnegative5933 p) (nonnegative5932 p)
def d5935 (p : Pattern) : Int := if p 163 then d1729 p else d1966 p
theorem agree5935 (p q : Pattern) (h : Agree support p q) : d5935 p = d5935 q := by
  simp only [d5935, h 163 (by decide), agree1729 p q h, agree1966 p q h]
theorem nonnegative5935 (p : Pattern) : 0 ≤ d5935 p :=
  nonnegative_ite (p 163) (nonnegative1729 p) (nonnegative1966 p)
def d5936 (p : Pattern) : Int := if p 162 then d12 p else d5935 p
theorem agree5936 (p q : Pattern) (h : Agree support p q) : d5936 p = d5936 q := by
  simp only [d5936, h 162 (by decide), agree12 p q h, agree5935 p q h]
theorem nonnegative5936 (p : Pattern) : 0 ≤ d5936 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5935 p)
def d5937 (p : Pattern) : Int := if p 161 then d5936 p else d5934 p
theorem agree5937 (p q : Pattern) (h : Agree support p q) : d5937 p = d5937 q := by
  simp only [d5937, h 161 (by decide), agree5936 p q h, agree5934 p q h]
theorem nonnegative5937 (p : Pattern) : 0 ≤ d5937 p :=
  nonnegative_ite (p 161) (nonnegative5936 p) (nonnegative5934 p)
def d5938 (p : Pattern) : Int := if p 160 then d5923 p else d5937 p
theorem agree5938 (p q : Pattern) (h : Agree support p q) : d5938 p = d5938 q := by
  simp only [d5938, h 160 (by decide), agree5923 p q h, agree5937 p q h]
theorem nonnegative5938 (p : Pattern) : 0 ≤ d5938 p :=
  nonnegative_ite (p 160) (nonnegative5923 p) (nonnegative5937 p)
def d5939 (p : Pattern) : Int := if p 141 then d5938 p else d5931 p
theorem agree5939 (p q : Pattern) (h : Agree support p q) : d5939 p = d5939 q := by
  simp only [d5939, h 141 (by decide), agree5938 p q h, agree5931 p q h]
theorem nonnegative5939 (p : Pattern) : 0 ≤ d5939 p :=
  nonnegative_ite (p 141) (nonnegative5938 p) (nonnegative5931 p)
def d5940 (p : Pattern) : Int := if p 138 then d5939 p else d5925 p
theorem agree5940 (p q : Pattern) (h : Agree support p q) : d5940 p = d5940 q := by
  simp only [d5940, h 138 (by decide), agree5939 p q h, agree5925 p q h]
theorem nonnegative5940 (p : Pattern) : 0 ≤ d5940 p :=
  nonnegative_ite (p 138) (nonnegative5939 p) (nonnegative5925 p)
def d5941 (p : Pattern) : Int := if p 162 then d12 p else d5908 p
theorem agree5941 (p q : Pattern) (h : Agree support p q) : d5941 p = d5941 q := by
  simp only [d5941, h 162 (by decide), agree12 p q h, agree5908 p q h]
theorem nonnegative5941 (p : Pattern) : 0 ≤ d5941 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5908 p)
def d5942 (p : Pattern) : Int := if p 161 then d12 p else d5941 p
theorem agree5942 (p q : Pattern) (h : Agree support p q) : d5942 p = d5942 q := by
  simp only [d5942, h 161 (by decide), agree12 p q h, agree5941 p q h]
theorem nonnegative5942 (p : Pattern) : 0 ≤ d5942 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5941 p)
def d5943 (p : Pattern) : Int := if p 160 then d12 p else d5942 p
theorem agree5943 (p q : Pattern) (h : Agree support p q) : d5943 p = d5943 q := by
  simp only [d5943, h 160 (by decide), agree12 p q h, agree5942 p q h]
theorem nonnegative5943 (p : Pattern) : 0 ≤ d5943 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5942 p)
def d5944 (p : Pattern) : Int := if p 141 then d12 p else d5943 p
theorem agree5944 (p q : Pattern) (h : Agree support p q) : d5944 p = d5944 q := by
  simp only [d5944, h 141 (by decide), agree12 p q h, agree5943 p q h]
theorem nonnegative5944 (p : Pattern) : 0 ≤ d5944 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative5943 p)
def d5945 (p : Pattern) : Int := if p 138 then d5944 p else d5939 p
theorem agree5945 (p q : Pattern) (h : Agree support p q) : d5945 p = d5945 q := by
  simp only [d5945, h 138 (by decide), agree5944 p q h, agree5939 p q h]
theorem nonnegative5945 (p : Pattern) : 0 ≤ d5945 p :=
  nonnegative_ite (p 138) (nonnegative5944 p) (nonnegative5939 p)
def d5946 (p : Pattern) : Int := if p 116 then d5945 p else d5940 p
theorem agree5946 (p q : Pattern) (h : Agree support p q) : d5946 p = d5946 q := by
  simp only [d5946, h 116 (by decide), agree5945 p q h, agree5940 p q h]
theorem nonnegative5946 (p : Pattern) : 0 ≤ d5946 p :=
  nonnegative_ite (p 116) (nonnegative5945 p) (nonnegative5940 p)
def d5947 (p : Pattern) : Int := if p 138 then d12 p else d5939 p
theorem agree5947 (p q : Pattern) (h : Agree support p q) : d5947 p = d5947 q := by
  simp only [d5947, h 138 (by decide), agree12 p q h, agree5939 p q h]
theorem nonnegative5947 (p : Pattern) : 0 ≤ d5947 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5939 p)
def d5948 (p : Pattern) : Int := if p 116 then d5947 p else d5940 p
theorem agree5948 (p q : Pattern) (h : Agree support p q) : d5948 p = d5948 q := by
  simp only [d5948, h 116 (by decide), agree5947 p q h, agree5940 p q h]
theorem nonnegative5948 (p : Pattern) : 0 ≤ d5948 p :=
  nonnegative_ite (p 116) (nonnegative5947 p) (nonnegative5940 p)
def d5949 (p : Pattern) : Int := if p 115 then d5948 p else d5946 p
theorem agree5949 (p q : Pattern) (h : Agree support p q) : d5949 p = d5949 q := by
  simp only [d5949, h 115 (by decide), agree5948 p q h, agree5946 p q h]
theorem nonnegative5949 (p : Pattern) : 0 ≤ d5949 p :=
  nonnegative_ite (p 115) (nonnegative5948 p) (nonnegative5946 p)
def d5950 (p : Pattern) : Int := if p 71 then d5949 p else d5905 p
theorem agree5950 (p q : Pattern) (h : Agree support p q) : d5950 p = d5950 q := by
  simp only [d5950, h 71 (by decide), agree5949 p q h, agree5905 p q h]
theorem nonnegative5950 (p : Pattern) : 0 ≤ d5950 p :=
  nonnegative_ite (p 71) (nonnegative5949 p) (nonnegative5905 p)
def d5951 (p : Pattern) : Int := if p 49 then d5950 p else d5905 p
theorem agree5951 (p q : Pattern) (h : Agree support p q) : d5951 p = d5951 q := by
  simp only [d5951, h 49 (by decide), agree5950 p q h, agree5905 p q h]
theorem nonnegative5951 (p : Pattern) : 0 ≤ d5951 p :=
  nonnegative_ite (p 49) (nonnegative5950 p) (nonnegative5905 p)
def d5952 (p : Pattern) : Int := if p 163 then d2012 p else d1772 p
theorem agree5952 (p q : Pattern) (h : Agree support p q) : d5952 p = d5952 q := by
  simp only [d5952, h 163 (by decide), agree2012 p q h, agree1772 p q h]
theorem nonnegative5952 (p : Pattern) : 0 ≤ d5952 p :=
  nonnegative_ite (p 163) (nonnegative2012 p) (nonnegative1772 p)
def d5953 (p : Pattern) : Int := if p 162 then d5952 p else d1772 p
theorem agree5953 (p q : Pattern) (h : Agree support p q) : d5953 p = d5953 q := by
  simp only [d5953, h 162 (by decide), agree5952 p q h, agree1772 p q h]
theorem nonnegative5953 (p : Pattern) : 0 ≤ d5953 p :=
  nonnegative_ite (p 162) (nonnegative5952 p) (nonnegative1772 p)
def d5954 (p : Pattern) : Int := if p 162 then d5880 p else d5952 p
theorem agree5954 (p q : Pattern) (h : Agree support p q) : d5954 p = d5954 q := by
  simp only [d5954, h 162 (by decide), agree5880 p q h, agree5952 p q h]
theorem nonnegative5954 (p : Pattern) : 0 ≤ d5954 p :=
  nonnegative_ite (p 162) (nonnegative5880 p) (nonnegative5952 p)
def d5955 (p : Pattern) : Int := if p 161 then d5954 p else d5953 p
theorem agree5955 (p q : Pattern) (h : Agree support p q) : d5955 p = d5955 q := by
  simp only [d5955, h 161 (by decide), agree5954 p q h, agree5953 p q h]
theorem nonnegative5955 (p : Pattern) : 0 ≤ d5955 p :=
  nonnegative_ite (p 161) (nonnegative5954 p) (nonnegative5953 p)
def d5956 (p : Pattern) : Int := if p 160 then d5864 p else d5955 p
theorem agree5956 (p q : Pattern) (h : Agree support p q) : d5956 p = d5956 q := by
  simp only [d5956, h 160 (by decide), agree5864 p q h, agree5955 p q h]
theorem nonnegative5956 (p : Pattern) : 0 ≤ d5956 p :=
  nonnegative_ite (p 160) (nonnegative5864 p) (nonnegative5955 p)
def d5957 (p : Pattern) : Int := if p 163 then d2030 p else d1772 p
theorem agree5957 (p q : Pattern) (h : Agree support p q) : d5957 p = d5957 q := by
  simp only [d5957, h 163 (by decide), agree2030 p q h, agree1772 p q h]
theorem nonnegative5957 (p : Pattern) : 0 ≤ d5957 p :=
  nonnegative_ite (p 163) (nonnegative2030 p) (nonnegative1772 p)
def d5958 (p : Pattern) : Int := if p 163 then d1803 p else d2012 p
theorem agree5958 (p q : Pattern) (h : Agree support p q) : d5958 p = d5958 q := by
  simp only [d5958, h 163 (by decide), agree1803 p q h, agree2012 p q h]
theorem nonnegative5958 (p : Pattern) : 0 ≤ d5958 p :=
  nonnegative_ite (p 163) (nonnegative1803 p) (nonnegative2012 p)
def d5959 (p : Pattern) : Int := if p 162 then d5958 p else d5957 p
theorem agree5959 (p q : Pattern) (h : Agree support p q) : d5959 p = d5959 q := by
  simp only [d5959, h 162 (by decide), agree5958 p q h, agree5957 p q h]
theorem nonnegative5959 (p : Pattern) : 0 ≤ d5959 p :=
  nonnegative_ite (p 162) (nonnegative5958 p) (nonnegative5957 p)
def d5960 (p : Pattern) : Int := if p 163 then d1752 p else d2012 p
theorem agree5960 (p q : Pattern) (h : Agree support p q) : d5960 p = d5960 q := by
  simp only [d5960, h 163 (by decide), agree1752 p q h, agree2012 p q h]
theorem nonnegative5960 (p : Pattern) : 0 ≤ d5960 p :=
  nonnegative_ite (p 163) (nonnegative1752 p) (nonnegative2012 p)
def d5961 (p : Pattern) : Int := if p 162 then d5862 p else d5960 p
theorem agree5961 (p q : Pattern) (h : Agree support p q) : d5961 p = d5961 q := by
  simp only [d5961, h 162 (by decide), agree5862 p q h, agree5960 p q h]
theorem nonnegative5961 (p : Pattern) : 0 ≤ d5961 p :=
  nonnegative_ite (p 162) (nonnegative5862 p) (nonnegative5960 p)
def d5962 (p : Pattern) : Int := if p 161 then d5961 p else d5959 p
theorem agree5962 (p q : Pattern) (h : Agree support p q) : d5962 p = d5962 q := by
  simp only [d5962, h 161 (by decide), agree5961 p q h, agree5959 p q h]
theorem nonnegative5962 (p : Pattern) : 0 ≤ d5962 p :=
  nonnegative_ite (p 161) (nonnegative5961 p) (nonnegative5959 p)
def d5963 (p : Pattern) : Int := if p 160 then d5874 p else d5962 p
theorem agree5963 (p q : Pattern) (h : Agree support p q) : d5963 p = d5963 q := by
  simp only [d5963, h 160 (by decide), agree5874 p q h, agree5962 p q h]
theorem nonnegative5963 (p : Pattern) : 0 ≤ d5963 p :=
  nonnegative_ite (p 160) (nonnegative5874 p) (nonnegative5962 p)
def d5964 (p : Pattern) : Int := if p 141 then d5963 p else d5956 p
theorem agree5964 (p q : Pattern) (h : Agree support p q) : d5964 p = d5964 q := by
  simp only [d5964, h 141 (by decide), agree5963 p q h, agree5956 p q h]
theorem nonnegative5964 (p : Pattern) : 0 ≤ d5964 p :=
  nonnegative_ite (p 141) (nonnegative5963 p) (nonnegative5956 p)
def d5965 (p : Pattern) : Int := if p 163 then d2054 p else d2048 p
theorem agree5965 (p q : Pattern) (h : Agree support p q) : d5965 p = d5965 q := by
  simp only [d5965, h 163 (by decide), agree2054 p q h, agree2048 p q h]
theorem nonnegative5965 (p : Pattern) : 0 ≤ d5965 p :=
  nonnegative_ite (p 163) (nonnegative2054 p) (nonnegative2048 p)
def d5966 (p : Pattern) : Int := if p 162 then d5861 p else d5965 p
theorem agree5966 (p q : Pattern) (h : Agree support p q) : d5966 p = d5966 q := by
  simp only [d5966, h 162 (by decide), agree5861 p q h, agree5965 p q h]
theorem nonnegative5966 (p : Pattern) : 0 ≤ d5966 p :=
  nonnegative_ite (p 162) (nonnegative5861 p) (nonnegative5965 p)
def d5967 (p : Pattern) : Int := if p 161 then d5863 p else d5966 p
theorem agree5967 (p q : Pattern) (h : Agree support p q) : d5967 p = d5967 q := by
  simp only [d5967, h 161 (by decide), agree5863 p q h, agree5966 p q h]
theorem nonnegative5967 (p : Pattern) : 0 ≤ d5967 p :=
  nonnegative_ite (p 161) (nonnegative5863 p) (nonnegative5966 p)
def d5968 (p : Pattern) : Int := if p 163 then d2061 p else d1797 p
theorem agree5968 (p q : Pattern) (h : Agree support p q) : d5968 p = d5968 q := by
  simp only [d5968, h 163 (by decide), agree2061 p q h, agree1797 p q h]
theorem nonnegative5968 (p : Pattern) : 0 ≤ d5968 p :=
  nonnegative_ite (p 163) (nonnegative2061 p) (nonnegative1797 p)
def d5969 (p : Pattern) : Int := if p 162 then d12 p else d5968 p
theorem agree5969 (p q : Pattern) (h : Agree support p q) : d5969 p = d5969 q := by
  simp only [d5969, h 162 (by decide), agree12 p q h, agree5968 p q h]
theorem nonnegative5969 (p : Pattern) : 0 ≤ d5969 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5968 p)
def d5970 (p : Pattern) : Int := if p 161 then d12 p else d5969 p
theorem agree5970 (p q : Pattern) (h : Agree support p q) : d5970 p = d5970 q := by
  simp only [d5970, h 161 (by decide), agree12 p q h, agree5969 p q h]
theorem nonnegative5970 (p : Pattern) : 0 ≤ d5970 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5969 p)
def d5971 (p : Pattern) : Int := if p 160 then d5970 p else d5967 p
theorem agree5971 (p q : Pattern) (h : Agree support p q) : d5971 p = d5971 q := by
  simp only [d5971, h 160 (by decide), agree5970 p q h, agree5967 p q h]
theorem nonnegative5971 (p : Pattern) : 0 ≤ d5971 p :=
  nonnegative_ite (p 160) (nonnegative5970 p) (nonnegative5967 p)
def d5972 (p : Pattern) : Int := if p 163 then d1717 p else d2071 p
theorem agree5972 (p q : Pattern) (h : Agree support p q) : d5972 p = d5972 q := by
  simp only [d5972, h 163 (by decide), agree1717 p q h, agree2071 p q h]
theorem nonnegative5972 (p : Pattern) : 0 ≤ d5972 p :=
  nonnegative_ite (p 163) (nonnegative1717 p) (nonnegative2071 p)
def d5973 (p : Pattern) : Int := if p 163 then d1729 p else d1797 p
theorem agree5973 (p q : Pattern) (h : Agree support p q) : d5973 p = d5973 q := by
  simp only [d5973, h 163 (by decide), agree1729 p q h, agree1797 p q h]
theorem nonnegative5973 (p : Pattern) : 0 ≤ d5973 p :=
  nonnegative_ite (p 163) (nonnegative1729 p) (nonnegative1797 p)
def d5974 (p : Pattern) : Int := if p 162 then d5973 p else d5972 p
theorem agree5974 (p q : Pattern) (h : Agree support p q) : d5974 p = d5974 q := by
  simp only [d5974, h 162 (by decide), agree5973 p q h, agree5972 p q h]
theorem nonnegative5974 (p : Pattern) : 0 ≤ d5974 p :=
  nonnegative_ite (p 162) (nonnegative5973 p) (nonnegative5972 p)
def d5975 (p : Pattern) : Int := if p 161 then d5873 p else d5974 p
theorem agree5975 (p q : Pattern) (h : Agree support p q) : d5975 p = d5975 q := by
  simp only [d5975, h 161 (by decide), agree5873 p q h, agree5974 p q h]
theorem nonnegative5975 (p : Pattern) : 0 ≤ d5975 p :=
  nonnegative_ite (p 161) (nonnegative5873 p) (nonnegative5974 p)
def d5976 (p : Pattern) : Int := if p 163 then d12 p else d2061 p
theorem agree5976 (p q : Pattern) (h : Agree support p q) : d5976 p = d5976 q := by
  simp only [d5976, h 163 (by decide), agree12 p q h, agree2061 p q h]
theorem nonnegative5976 (p : Pattern) : 0 ≤ d5976 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2061 p)
def d5977 (p : Pattern) : Int := if p 162 then d12 p else d5976 p
theorem agree5977 (p q : Pattern) (h : Agree support p q) : d5977 p = d5977 q := by
  simp only [d5977, h 162 (by decide), agree12 p q h, agree5976 p q h]
theorem nonnegative5977 (p : Pattern) : 0 ≤ d5977 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5976 p)
def d5978 (p : Pattern) : Int := if p 161 then d12 p else d5977 p
theorem agree5978 (p q : Pattern) (h : Agree support p q) : d5978 p = d5978 q := by
  simp only [d5978, h 161 (by decide), agree12 p q h, agree5977 p q h]
theorem nonnegative5978 (p : Pattern) : 0 ≤ d5978 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5977 p)
def d5979 (p : Pattern) : Int := if p 160 then d5978 p else d5975 p
theorem agree5979 (p q : Pattern) (h : Agree support p q) : d5979 p = d5979 q := by
  simp only [d5979, h 160 (by decide), agree5978 p q h, agree5975 p q h]
theorem nonnegative5979 (p : Pattern) : 0 ≤ d5979 p :=
  nonnegative_ite (p 160) (nonnegative5978 p) (nonnegative5975 p)
def d5980 (p : Pattern) : Int := if p 141 then d5979 p else d5971 p
theorem agree5980 (p q : Pattern) (h : Agree support p q) : d5980 p = d5980 q := by
  simp only [d5980, h 141 (by decide), agree5979 p q h, agree5971 p q h]
theorem nonnegative5980 (p : Pattern) : 0 ≤ d5980 p :=
  nonnegative_ite (p 141) (nonnegative5979 p) (nonnegative5971 p)
def d5981 (p : Pattern) : Int := if p 138 then d5980 p else d5964 p
theorem agree5981 (p q : Pattern) (h : Agree support p q) : d5981 p = d5981 q := by
  simp only [d5981, h 138 (by decide), agree5980 p q h, agree5964 p q h]
theorem nonnegative5981 (p : Pattern) : 0 ≤ d5981 p :=
  nonnegative_ite (p 138) (nonnegative5980 p) (nonnegative5964 p)
def d5982 (p : Pattern) : Int := if p 138 then d12 p else d5980 p
theorem agree5982 (p q : Pattern) (h : Agree support p q) : d5982 p = d5982 q := by
  simp only [d5982, h 138 (by decide), agree12 p q h, agree5980 p q h]
theorem nonnegative5982 (p : Pattern) : 0 ≤ d5982 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5980 p)
def d5983 (p : Pattern) : Int := if p 116 then d5982 p else d5981 p
theorem agree5983 (p q : Pattern) (h : Agree support p q) : d5983 p = d5983 q := by
  simp only [d5983, h 116 (by decide), agree5982 p q h, agree5981 p q h]
theorem nonnegative5983 (p : Pattern) : 0 ≤ d5983 p :=
  nonnegative_ite (p 116) (nonnegative5982 p) (nonnegative5981 p)
def d5984 (p : Pattern) : Int := if p 115 then d5983 p else d5902 p
theorem agree5984 (p q : Pattern) (h : Agree support p q) : d5984 p = d5984 q := by
  simp only [d5984, h 115 (by decide), agree5983 p q h, agree5902 p q h]
theorem nonnegative5984 (p : Pattern) : 0 ≤ d5984 p :=
  nonnegative_ite (p 115) (nonnegative5983 p) (nonnegative5902 p)
def d5985 (p : Pattern) : Int := if p 71 then d5984 p else d5905 p
theorem agree5985 (p q : Pattern) (h : Agree support p q) : d5985 p = d5985 q := by
  simp only [d5985, h 71 (by decide), agree5984 p q h, agree5905 p q h]
theorem nonnegative5985 (p : Pattern) : 0 ≤ d5985 p :=
  nonnegative_ite (p 71) (nonnegative5984 p) (nonnegative5905 p)
def d5986 (p : Pattern) : Int := if p 163 then d12 p else d1883 p
theorem agree5986 (p q : Pattern) (h : Agree support p q) : d5986 p = d5986 q := by
  simp only [d5986, h 163 (by decide), agree12 p q h, agree1883 p q h]
theorem nonnegative5986 (p : Pattern) : 0 ≤ d5986 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1883 p)
def d5987 (p : Pattern) : Int := if p 162 then d5986 p else d5915 p
theorem agree5987 (p q : Pattern) (h : Agree support p q) : d5987 p = d5987 q := by
  simp only [d5987, h 162 (by decide), agree5986 p q h, agree5915 p q h]
theorem nonnegative5987 (p : Pattern) : 0 ≤ d5987 p :=
  nonnegative_ite (p 162) (nonnegative5986 p) (nonnegative5915 p)
def d5988 (p : Pattern) : Int := if p 162 then d12 p else d5986 p
theorem agree5988 (p q : Pattern) (h : Agree support p q) : d5988 p = d5988 q := by
  simp only [d5988, h 162 (by decide), agree12 p q h, agree5986 p q h]
theorem nonnegative5988 (p : Pattern) : 0 ≤ d5988 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5986 p)
def d5989 (p : Pattern) : Int := if p 161 then d5988 p else d5987 p
theorem agree5989 (p q : Pattern) (h : Agree support p q) : d5989 p = d5989 q := by
  simp only [d5989, h 161 (by decide), agree5988 p q h, agree5987 p q h]
theorem nonnegative5989 (p : Pattern) : 0 ≤ d5989 p :=
  nonnegative_ite (p 161) (nonnegative5988 p) (nonnegative5987 p)
def d5990 (p : Pattern) : Int := if p 160 then d5923 p else d5989 p
theorem agree5990 (p q : Pattern) (h : Agree support p q) : d5990 p = d5990 q := by
  simp only [d5990, h 160 (by decide), agree5923 p q h, agree5989 p q h]
theorem nonnegative5990 (p : Pattern) : 0 ≤ d5990 p :=
  nonnegative_ite (p 160) (nonnegative5923 p) (nonnegative5989 p)
def d5991 (p : Pattern) : Int := if p 141 then d5990 p else d5914 p
theorem agree5991 (p q : Pattern) (h : Agree support p q) : d5991 p = d5991 q := by
  simp only [d5991, h 141 (by decide), agree5990 p q h, agree5914 p q h]
theorem nonnegative5991 (p : Pattern) : 0 ≤ d5991 p :=
  nonnegative_ite (p 141) (nonnegative5990 p) (nonnegative5914 p)
def d5992 (p : Pattern) : Int := if p 163 then d12 p else d1966 p
theorem agree5992 (p q : Pattern) (h : Agree support p q) : d5992 p = d5992 q := by
  simp only [d5992, h 163 (by decide), agree12 p q h, agree1966 p q h]
theorem nonnegative5992 (p : Pattern) : 0 ≤ d5992 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1966 p)
def d5993 (p : Pattern) : Int := if p 162 then d5992 p else d5932 p
theorem agree5993 (p q : Pattern) (h : Agree support p q) : d5993 p = d5993 q := by
  simp only [d5993, h 162 (by decide), agree5992 p q h, agree5932 p q h]
theorem nonnegative5993 (p : Pattern) : 0 ≤ d5993 p :=
  nonnegative_ite (p 162) (nonnegative5992 p) (nonnegative5932 p)
def d5994 (p : Pattern) : Int := if p 162 then d12 p else d5992 p
theorem agree5994 (p q : Pattern) (h : Agree support p q) : d5994 p = d5994 q := by
  simp only [d5994, h 162 (by decide), agree12 p q h, agree5992 p q h]
theorem nonnegative5994 (p : Pattern) : 0 ≤ d5994 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5992 p)
def d5995 (p : Pattern) : Int := if p 161 then d5994 p else d5993 p
theorem agree5995 (p q : Pattern) (h : Agree support p q) : d5995 p = d5995 q := by
  simp only [d5995, h 161 (by decide), agree5994 p q h, agree5993 p q h]
theorem nonnegative5995 (p : Pattern) : 0 ≤ d5995 p :=
  nonnegative_ite (p 161) (nonnegative5994 p) (nonnegative5993 p)
def d5996 (p : Pattern) : Int := if p 160 then d5923 p else d5995 p
theorem agree5996 (p q : Pattern) (h : Agree support p q) : d5996 p = d5996 q := by
  simp only [d5996, h 160 (by decide), agree5923 p q h, agree5995 p q h]
theorem nonnegative5996 (p : Pattern) : 0 ≤ d5996 p :=
  nonnegative_ite (p 160) (nonnegative5923 p) (nonnegative5995 p)
def d5997 (p : Pattern) : Int := if p 141 then d5996 p else d5931 p
theorem agree5997 (p q : Pattern) (h : Agree support p q) : d5997 p = d5997 q := by
  simp only [d5997, h 141 (by decide), agree5996 p q h, agree5931 p q h]
theorem nonnegative5997 (p : Pattern) : 0 ≤ d5997 p :=
  nonnegative_ite (p 141) (nonnegative5996 p) (nonnegative5931 p)
def d5998 (p : Pattern) : Int := if p 138 then d5997 p else d5991 p
theorem agree5998 (p q : Pattern) (h : Agree support p q) : d5998 p = d5998 q := by
  simp only [d5998, h 138 (by decide), agree5997 p q h, agree5991 p q h]
theorem nonnegative5998 (p : Pattern) : 0 ≤ d5998 p :=
  nonnegative_ite (p 138) (nonnegative5997 p) (nonnegative5991 p)
def d5999 (p : Pattern) : Int := if p 138 then d5944 p else d5997 p
theorem agree5999 (p q : Pattern) (h : Agree support p q) : d5999 p = d5999 q := by
  simp only [d5999, h 138 (by decide), agree5944 p q h, agree5997 p q h]
theorem nonnegative5999 (p : Pattern) : 0 ≤ d5999 p :=
  nonnegative_ite (p 138) (nonnegative5944 p) (nonnegative5997 p)
end NetHack.Sokoban22Refined85
