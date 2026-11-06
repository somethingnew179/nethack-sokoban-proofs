/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes49
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6000 (p : Pattern) : Int := if p 116 then d5999 p else d5998 p
theorem agree6000 (p q : Pattern) (h : Agree support p q) : d6000 p = d6000 q := by
  simp only [d6000, h 116 (by decide), agree5999 p q h, agree5998 p q h]
theorem nonnegative6000 (p : Pattern) : 0 ≤ d6000 p :=
  nonnegative_ite (p 116) (nonnegative5999 p) (nonnegative5998 p)
def d6001 (p : Pattern) : Int := if p 163 then d1966 p else d2108 p
theorem agree6001 (p q : Pattern) (h : Agree support p q) : d6001 p = d6001 q := by
  simp only [d6001, h 163 (by decide), agree1966 p q h, agree2108 p q h]
theorem nonnegative6001 (p : Pattern) : 0 ≤ d6001 p :=
  nonnegative_ite (p 163) (nonnegative1966 p) (nonnegative2108 p)
def d6002 (p : Pattern) : Int := if p 162 then d6001 p else d1942 p
theorem agree6002 (p q : Pattern) (h : Agree support p q) : d6002 p = d6002 q := by
  simp only [d6002, h 162 (by decide), agree6001 p q h, agree1942 p q h]
theorem nonnegative6002 (p : Pattern) : 0 ≤ d6002 p :=
  nonnegative_ite (p 162) (nonnegative6001 p) (nonnegative1942 p)
def d6003 (p : Pattern) : Int := if p 163 then d1966 p else d1951 p
theorem agree6003 (p q : Pattern) (h : Agree support p q) : d6003 p = d6003 q := by
  simp only [d6003, h 163 (by decide), agree1966 p q h, agree1951 p q h]
theorem nonnegative6003 (p : Pattern) : 0 ≤ d6003 p :=
  nonnegative_ite (p 163) (nonnegative1966 p) (nonnegative1951 p)
def d6004 (p : Pattern) : Int := if p 162 then d5908 p else d6003 p
theorem agree6004 (p q : Pattern) (h : Agree support p q) : d6004 p = d6004 q := by
  simp only [d6004, h 162 (by decide), agree5908 p q h, agree6003 p q h]
theorem nonnegative6004 (p : Pattern) : 0 ≤ d6004 p :=
  nonnegative_ite (p 162) (nonnegative5908 p) (nonnegative6003 p)
def d6005 (p : Pattern) : Int := if p 161 then d6004 p else d6002 p
theorem agree6005 (p q : Pattern) (h : Agree support p q) : d6005 p = d6005 q := by
  simp only [d6005, h 161 (by decide), agree6004 p q h, agree6002 p q h]
theorem nonnegative6005 (p : Pattern) : 0 ≤ d6005 p :=
  nonnegative_ite (p 161) (nonnegative6004 p) (nonnegative6002 p)
def d6006 (p : Pattern) : Int := if p 160 then d5913 p else d6005 p
theorem agree6006 (p q : Pattern) (h : Agree support p q) : d6006 p = d6006 q := by
  simp only [d6006, h 160 (by decide), agree5913 p q h, agree6005 p q h]
theorem nonnegative6006 (p : Pattern) : 0 ≤ d6006 p :=
  nonnegative_ite (p 160) (nonnegative5913 p) (nonnegative6005 p)
def d6007 (p : Pattern) : Int := if p 163 then d2125 p else d2108 p
theorem agree6007 (p q : Pattern) (h : Agree support p q) : d6007 p = d6007 q := by
  simp only [d6007, h 163 (by decide), agree2125 p q h, agree2108 p q h]
theorem nonnegative6007 (p : Pattern) : 0 ≤ d6007 p :=
  nonnegative_ite (p 163) (nonnegative2125 p) (nonnegative2108 p)
def d6008 (p : Pattern) : Int := if p 163 then d12 p else d2130 p
theorem agree6008 (p q : Pattern) (h : Agree support p q) : d6008 p = d6008 q := by
  simp only [d6008, h 163 (by decide), agree12 p q h, agree2130 p q h]
theorem nonnegative6008 (p : Pattern) : 0 ≤ d6008 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2130 p)
def d6009 (p : Pattern) : Int := if p 162 then d6008 p else d6007 p
theorem agree6009 (p q : Pattern) (h : Agree support p q) : d6009 p = d6009 q := by
  simp only [d6009, h 162 (by decide), agree6008 p q h, agree6007 p q h]
theorem nonnegative6009 (p : Pattern) : 0 ≤ d6009 p :=
  nonnegative_ite (p 162) (nonnegative6008 p) (nonnegative6007 p)
def d6010 (p : Pattern) : Int := if p 163 then d12 p else d2136 p
theorem agree6010 (p q : Pattern) (h : Agree support p q) : d6010 p = d6010 q := by
  simp only [d6010, h 163 (by decide), agree12 p q h, agree2136 p q h]
theorem nonnegative6010 (p : Pattern) : 0 ≤ d6010 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2136 p)
def d6011 (p : Pattern) : Int := if p 162 then d12 p else d6010 p
theorem agree6011 (p q : Pattern) (h : Agree support p q) : d6011 p = d6011 q := by
  simp only [d6011, h 162 (by decide), agree12 p q h, agree6010 p q h]
theorem nonnegative6011 (p : Pattern) : 0 ≤ d6011 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6010 p)
def d6012 (p : Pattern) : Int := if p 161 then d6011 p else d6009 p
theorem agree6012 (p q : Pattern) (h : Agree support p q) : d6012 p = d6012 q := by
  simp only [d6012, h 161 (by decide), agree6011 p q h, agree6009 p q h]
theorem nonnegative6012 (p : Pattern) : 0 ≤ d6012 p :=
  nonnegative_ite (p 161) (nonnegative6011 p) (nonnegative6009 p)
def d6013 (p : Pattern) : Int := if p 160 then d5923 p else d6012 p
theorem agree6013 (p q : Pattern) (h : Agree support p q) : d6013 p = d6013 q := by
  simp only [d6013, h 160 (by decide), agree5923 p q h, agree6012 p q h]
theorem nonnegative6013 (p : Pattern) : 0 ≤ d6013 p :=
  nonnegative_ite (p 160) (nonnegative5923 p) (nonnegative6012 p)
def d6014 (p : Pattern) : Int := if p 141 then d6013 p else d6006 p
theorem agree6014 (p q : Pattern) (h : Agree support p q) : d6014 p = d6014 q := by
  simp only [d6014, h 141 (by decide), agree6013 p q h, agree6006 p q h]
theorem nonnegative6014 (p : Pattern) : 0 ≤ d6014 p :=
  nonnegative_ite (p 141) (nonnegative6013 p) (nonnegative6006 p)
def d6015 (p : Pattern) : Int := if p 163 then d1957 p else d1951 p
theorem agree6015 (p q : Pattern) (h : Agree support p q) : d6015 p = d6015 q := by
  simp only [d6015, h 163 (by decide), agree1957 p q h, agree1951 p q h]
theorem nonnegative6015 (p : Pattern) : 0 ≤ d6015 p :=
  nonnegative_ite (p 163) (nonnegative1957 p) (nonnegative1951 p)
def d6016 (p : Pattern) : Int := if p 163 then d1729 p else d1898 p
theorem agree6016 (p q : Pattern) (h : Agree support p q) : d6016 p = d6016 q := by
  simp only [d6016, h 163 (by decide), agree1729 p q h, agree1898 p q h]
theorem nonnegative6016 (p : Pattern) : 0 ≤ d6016 p :=
  nonnegative_ite (p 163) (nonnegative1729 p) (nonnegative1898 p)
def d6017 (p : Pattern) : Int := if p 162 then d6016 p else d6015 p
theorem agree6017 (p q : Pattern) (h : Agree support p q) : d6017 p = d6017 q := by
  simp only [d6017, h 162 (by decide), agree6016 p q h, agree6015 p q h]
theorem nonnegative6017 (p : Pattern) : 0 ≤ d6017 p :=
  nonnegative_ite (p 162) (nonnegative6016 p) (nonnegative6015 p)
def d6018 (p : Pattern) : Int := if p 161 then d5936 p else d6017 p
theorem agree6018 (p q : Pattern) (h : Agree support p q) : d6018 p = d6018 q := by
  simp only [d6018, h 161 (by decide), agree5936 p q h, agree6017 p q h]
theorem nonnegative6018 (p : Pattern) : 0 ≤ d6018 p :=
  nonnegative_ite (p 161) (nonnegative5936 p) (nonnegative6017 p)
def d6019 (p : Pattern) : Int := if p 160 then d5923 p else d6018 p
theorem agree6019 (p q : Pattern) (h : Agree support p q) : d6019 p = d6019 q := by
  simp only [d6019, h 160 (by decide), agree5923 p q h, agree6018 p q h]
theorem nonnegative6019 (p : Pattern) : 0 ≤ d6019 p :=
  nonnegative_ite (p 160) (nonnegative5923 p) (nonnegative6018 p)
def d6020 (p : Pattern) : Int := if p 163 then d1898 p else d2157 p
theorem agree6020 (p q : Pattern) (h : Agree support p q) : d6020 p = d6020 q := by
  simp only [d6020, h 163 (by decide), agree1898 p q h, agree2157 p q h]
theorem nonnegative6020 (p : Pattern) : 0 ≤ d6020 p :=
  nonnegative_ite (p 163) (nonnegative1898 p) (nonnegative2157 p)
def d6021 (p : Pattern) : Int := if p 162 then d5992 p else d6020 p
theorem agree6021 (p q : Pattern) (h : Agree support p q) : d6021 p = d6021 q := by
  simp only [d6021, h 162 (by decide), agree5992 p q h, agree6020 p q h]
theorem nonnegative6021 (p : Pattern) : 0 ≤ d6021 p :=
  nonnegative_ite (p 162) (nonnegative5992 p) (nonnegative6020 p)
def d6022 (p : Pattern) : Int := if p 161 then d5922 p else d6021 p
theorem agree6022 (p q : Pattern) (h : Agree support p q) : d6022 p = d6022 q := by
  simp only [d6022, h 161 (by decide), agree5922 p q h, agree6021 p q h]
theorem nonnegative6022 (p : Pattern) : 0 ≤ d6022 p :=
  nonnegative_ite (p 161) (nonnegative5922 p) (nonnegative6021 p)
def d6023 (p : Pattern) : Int := if p 162 then d12 p else d5880 p
theorem agree6023 (p q : Pattern) (h : Agree support p q) : d6023 p = d6023 q := by
  simp only [d6023, h 162 (by decide), agree12 p q h, agree5880 p q h]
theorem nonnegative6023 (p : Pattern) : 0 ≤ d6023 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5880 p)
def d6024 (p : Pattern) : Int := if p 161 then d12 p else d6023 p
theorem agree6024 (p q : Pattern) (h : Agree support p q) : d6024 p = d6024 q := by
  simp only [d6024, h 161 (by decide), agree12 p q h, agree6023 p q h]
theorem nonnegative6024 (p : Pattern) : 0 ≤ d6024 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6023 p)
def d6025 (p : Pattern) : Int := if p 160 then d6024 p else d6022 p
theorem agree6025 (p q : Pattern) (h : Agree support p q) : d6025 p = d6025 q := by
  simp only [d6025, h 160 (by decide), agree6024 p q h, agree6022 p q h]
theorem nonnegative6025 (p : Pattern) : 0 ≤ d6025 p :=
  nonnegative_ite (p 160) (nonnegative6024 p) (nonnegative6022 p)
def d6026 (p : Pattern) : Int := if p 141 then d6025 p else d6019 p
theorem agree6026 (p q : Pattern) (h : Agree support p q) : d6026 p = d6026 q := by
  simp only [d6026, h 141 (by decide), agree6025 p q h, agree6019 p q h]
theorem nonnegative6026 (p : Pattern) : 0 ≤ d6026 p :=
  nonnegative_ite (p 141) (nonnegative6025 p) (nonnegative6019 p)
def d6027 (p : Pattern) : Int := if p 138 then d6026 p else d6014 p
theorem agree6027 (p q : Pattern) (h : Agree support p q) : d6027 p = d6027 q := by
  simp only [d6027, h 138 (by decide), agree6026 p q h, agree6014 p q h]
theorem nonnegative6027 (p : Pattern) : 0 ≤ d6027 p :=
  nonnegative_ite (p 138) (nonnegative6026 p) (nonnegative6014 p)
def d6028 (p : Pattern) : Int := if p 163 then d1803 p else d1898 p
theorem agree6028 (p q : Pattern) (h : Agree support p q) : d6028 p = d6028 q := by
  simp only [d6028, h 163 (by decide), agree1803 p q h, agree1898 p q h]
theorem nonnegative6028 (p : Pattern) : 0 ≤ d6028 p :=
  nonnegative_ite (p 163) (nonnegative1803 p) (nonnegative1898 p)
def d6029 (p : Pattern) : Int := if p 162 then d6028 p else d6015 p
theorem agree6029 (p q : Pattern) (h : Agree support p q) : d6029 p = d6029 q := by
  simp only [d6029, h 162 (by decide), agree6028 p q h, agree6015 p q h]
theorem nonnegative6029 (p : Pattern) : 0 ≤ d6029 p :=
  nonnegative_ite (p 162) (nonnegative6028 p) (nonnegative6015 p)
def d6030 (p : Pattern) : Int := if p 163 then d1803 p else d1966 p
theorem agree6030 (p q : Pattern) (h : Agree support p q) : d6030 p = d6030 q := by
  simp only [d6030, h 163 (by decide), agree1803 p q h, agree1966 p q h]
theorem nonnegative6030 (p : Pattern) : 0 ≤ d6030 p :=
  nonnegative_ite (p 163) (nonnegative1803 p) (nonnegative1966 p)
def d6031 (p : Pattern) : Int := if p 162 then d12 p else d6030 p
theorem agree6031 (p q : Pattern) (h : Agree support p q) : d6031 p = d6031 q := by
  simp only [d6031, h 162 (by decide), agree12 p q h, agree6030 p q h]
theorem nonnegative6031 (p : Pattern) : 0 ≤ d6031 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6030 p)
def d6032 (p : Pattern) : Int := if p 161 then d6031 p else d6029 p
theorem agree6032 (p q : Pattern) (h : Agree support p q) : d6032 p = d6032 q := by
  simp only [d6032, h 161 (by decide), agree6031 p q h, agree6029 p q h]
theorem nonnegative6032 (p : Pattern) : 0 ≤ d6032 p :=
  nonnegative_ite (p 161) (nonnegative6031 p) (nonnegative6029 p)
def d6033 (p : Pattern) : Int := if p 163 then d1729 p else d1905 p
theorem agree6033 (p q : Pattern) (h : Agree support p q) : d6033 p = d6033 q := by
  simp only [d6033, h 163 (by decide), agree1729 p q h, agree1905 p q h]
theorem nonnegative6033 (p : Pattern) : 0 ≤ d6033 p :=
  nonnegative_ite (p 163) (nonnegative1729 p) (nonnegative1905 p)
def d6034 (p : Pattern) : Int := if p 162 then d12 p else d6033 p
theorem agree6034 (p q : Pattern) (h : Agree support p q) : d6034 p = d6034 q := by
  simp only [d6034, h 162 (by decide), agree12 p q h, agree6033 p q h]
theorem nonnegative6034 (p : Pattern) : 0 ≤ d6034 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6033 p)
def d6035 (p : Pattern) : Int := if p 161 then d12 p else d6034 p
theorem agree6035 (p q : Pattern) (h : Agree support p q) : d6035 p = d6035 q := by
  simp only [d6035, h 161 (by decide), agree12 p q h, agree6034 p q h]
theorem nonnegative6035 (p : Pattern) : 0 ≤ d6035 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6034 p)
def d6036 (p : Pattern) : Int := if p 160 then d6035 p else d6032 p
theorem agree6036 (p q : Pattern) (h : Agree support p q) : d6036 p = d6036 q := by
  simp only [d6036, h 160 (by decide), agree6035 p q h, agree6032 p q h]
theorem nonnegative6036 (p : Pattern) : 0 ≤ d6036 p :=
  nonnegative_ite (p 160) (nonnegative6035 p) (nonnegative6032 p)
def d6037 (p : Pattern) : Int := if p 141 then d6025 p else d6036 p
theorem agree6037 (p q : Pattern) (h : Agree support p q) : d6037 p = d6037 q := by
  simp only [d6037, h 141 (by decide), agree6025 p q h, agree6036 p q h]
theorem nonnegative6037 (p : Pattern) : 0 ≤ d6037 p :=
  nonnegative_ite (p 141) (nonnegative6025 p) (nonnegative6036 p)
def d6038 (p : Pattern) : Int := if p 138 then d12 p else d6037 p
theorem agree6038 (p q : Pattern) (h : Agree support p q) : d6038 p = d6038 q := by
  simp only [d6038, h 138 (by decide), agree12 p q h, agree6037 p q h]
theorem nonnegative6038 (p : Pattern) : 0 ≤ d6038 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6037 p)
def d6039 (p : Pattern) : Int := if p 116 then d6038 p else d6027 p
theorem agree6039 (p q : Pattern) (h : Agree support p q) : d6039 p = d6039 q := by
  simp only [d6039, h 116 (by decide), agree6038 p q h, agree6027 p q h]
theorem nonnegative6039 (p : Pattern) : 0 ≤ d6039 p :=
  nonnegative_ite (p 116) (nonnegative6038 p) (nonnegative6027 p)
def d6040 (p : Pattern) : Int := if p 115 then d6039 p else d6000 p
theorem agree6040 (p q : Pattern) (h : Agree support p q) : d6040 p = d6040 q := by
  simp only [d6040, h 115 (by decide), agree6039 p q h, agree6000 p q h]
theorem nonnegative6040 (p : Pattern) : 0 ≤ d6040 p :=
  nonnegative_ite (p 115) (nonnegative6039 p) (nonnegative6000 p)
def d6041 (p : Pattern) : Int := if p 71 then d6040 p else d5905 p
theorem agree6041 (p q : Pattern) (h : Agree support p q) : d6041 p = d6041 q := by
  simp only [d6041, h 71 (by decide), agree6040 p q h, agree5905 p q h]
theorem nonnegative6041 (p : Pattern) : 0 ≤ d6041 p :=
  nonnegative_ite (p 71) (nonnegative6040 p) (nonnegative5905 p)
def d6042 (p : Pattern) : Int := if p 49 then d6041 p else d5985 p
theorem agree6042 (p q : Pattern) (h : Agree support p q) : d6042 p = d6042 q := by
  simp only [d6042, h 49 (by decide), agree6041 p q h, agree5985 p q h]
theorem nonnegative6042 (p : Pattern) : 0 ≤ d6042 p :=
  nonnegative_ite (p 49) (nonnegative6041 p) (nonnegative5985 p)
def d6043 (p : Pattern) : Int := if p 48 then d6042 p else d5951 p
theorem agree6043 (p q : Pattern) (h : Agree support p q) : d6043 p = d6043 q := by
  simp only [d6043, h 48 (by decide), agree6042 p q h, agree5951 p q h]
theorem nonnegative6043 (p : Pattern) : 0 ≤ d6043 p :=
  nonnegative_ite (p 48) (nonnegative6042 p) (nonnegative5951 p)
def d6044 (p : Pattern) : Int := if p 204 then d1770 p else d14 p
theorem agree6044 (p q : Pattern) (h : Agree support p q) : d6044 p = d6044 q := by
  simp only [d6044, h 204 (by decide), agree1770 p q h, agree14 p q h]
theorem nonnegative6044 (p : Pattern) : 0 ≤ d6044 p :=
  nonnegative_ite (p 204) (nonnegative1770 p) (nonnegative14 p)
def d6045 (p : Pattern) : Int := if p 204 then d12 p else d1684 p
theorem agree6045 (p q : Pattern) (h : Agree support p q) : d6045 p = d6045 q := by
  simp only [d6045, h 204 (by decide), agree12 p q h, agree1684 p q h]
theorem nonnegative6045 (p : Pattern) : 0 ≤ d6045 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1684 p)
def d6046 (p : Pattern) : Int := if p 182 then d6045 p else d6044 p
theorem agree6046 (p q : Pattern) (h : Agree support p q) : d6046 p = d6046 q := by
  simp only [d6046, h 182 (by decide), agree6045 p q h, agree6044 p q h]
theorem nonnegative6046 (p : Pattern) : 0 ≤ d6046 p :=
  nonnegative_ite (p 182) (nonnegative6045 p) (nonnegative6044 p)
def d6047 (p : Pattern) : Int := if p 204 then d1795 p else d18 p
theorem agree6047 (p q : Pattern) (h : Agree support p q) : d6047 p = d6047 q := by
  simp only [d6047, h 204 (by decide), agree1795 p q h, agree18 p q h]
theorem nonnegative6047 (p : Pattern) : 0 ≤ d6047 p :=
  nonnegative_ite (p 204) (nonnegative1795 p) (nonnegative18 p)
def d6048 (p : Pattern) : Int := if p 204 then d12 p else d1694 p
theorem agree6048 (p q : Pattern) (h : Agree support p q) : d6048 p = d6048 q := by
  simp only [d6048, h 204 (by decide), agree12 p q h, agree1694 p q h]
theorem nonnegative6048 (p : Pattern) : 0 ≤ d6048 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1694 p)
def d6049 (p : Pattern) : Int := if p 182 then d6048 p else d6047 p
theorem agree6049 (p q : Pattern) (h : Agree support p q) : d6049 p = d6049 q := by
  simp only [d6049, h 182 (by decide), agree6048 p q h, agree6047 p q h]
theorem nonnegative6049 (p : Pattern) : 0 ≤ d6049 p :=
  nonnegative_ite (p 182) (nonnegative6048 p) (nonnegative6047 p)
def d6050 (p : Pattern) : Int := if p 163 then d6049 p else d6046 p
theorem agree6050 (p q : Pattern) (h : Agree support p q) : d6050 p = d6050 q := by
  simp only [d6050, h 163 (by decide), agree6049 p q h, agree6046 p q h]
theorem nonnegative6050 (p : Pattern) : 0 ≤ d6050 p :=
  nonnegative_ite (p 163) (nonnegative6049 p) (nonnegative6046 p)
def d6051 (p : Pattern) : Int := if p 162 then d6050 p else d6046 p
theorem agree6051 (p q : Pattern) (h : Agree support p q) : d6051 p = d6051 q := by
  simp only [d6051, h 162 (by decide), agree6050 p q h, agree6046 p q h]
theorem nonnegative6051 (p : Pattern) : 0 ≤ d6051 p :=
  nonnegative_ite (p 162) (nonnegative6050 p) (nonnegative6046 p)
def d6052 (p : Pattern) : Int := if p 204 then d356 p else d24 p
theorem agree6052 (p q : Pattern) (h : Agree support p q) : d6052 p = d6052 q := by
  simp only [d6052, h 204 (by decide), agree356 p q h, agree24 p q h]
theorem nonnegative6052 (p : Pattern) : 0 ≤ d6052 p :=
  nonnegative_ite (p 204) (nonnegative356 p) (nonnegative24 p)
def d6053 (p : Pattern) : Int := if p 204 then d12 p else d1702 p
theorem agree6053 (p q : Pattern) (h : Agree support p q) : d6053 p = d6053 q := by
  simp only [d6053, h 204 (by decide), agree12 p q h, agree1702 p q h]
theorem nonnegative6053 (p : Pattern) : 0 ≤ d6053 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1702 p)
def d6054 (p : Pattern) : Int := if p 182 then d6053 p else d6052 p
theorem agree6054 (p q : Pattern) (h : Agree support p q) : d6054 p = d6054 q := by
  simp only [d6054, h 182 (by decide), agree6053 p q h, agree6052 p q h]
theorem nonnegative6054 (p : Pattern) : 0 ≤ d6054 p :=
  nonnegative_ite (p 182) (nonnegative6053 p) (nonnegative6052 p)
def d6055 (p : Pattern) : Int := if p 163 then d12 p else d6054 p
theorem agree6055 (p q : Pattern) (h : Agree support p q) : d6055 p = d6055 q := by
  simp only [d6055, h 163 (by decide), agree12 p q h, agree6054 p q h]
theorem nonnegative6055 (p : Pattern) : 0 ≤ d6055 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6054 p)
def d6056 (p : Pattern) : Int := if p 162 then d6055 p else d6050 p
theorem agree6056 (p q : Pattern) (h : Agree support p q) : d6056 p = d6056 q := by
  simp only [d6056, h 162 (by decide), agree6055 p q h, agree6050 p q h]
theorem nonnegative6056 (p : Pattern) : 0 ≤ d6056 p :=
  nonnegative_ite (p 162) (nonnegative6055 p) (nonnegative6050 p)
def d6057 (p : Pattern) : Int := if p 161 then d6056 p else d6051 p
theorem agree6057 (p q : Pattern) (h : Agree support p q) : d6057 p = d6057 q := by
  simp only [d6057, h 161 (by decide), agree6056 p q h, agree6051 p q h]
theorem nonnegative6057 (p : Pattern) : 0 ≤ d6057 p :=
  nonnegative_ite (p 161) (nonnegative6056 p) (nonnegative6051 p)
def d6058 (p : Pattern) : Int := if p 204 then d12 p else d1714 p
theorem agree6058 (p q : Pattern) (h : Agree support p q) : d6058 p = d6058 q := by
  simp only [d6058, h 204 (by decide), agree12 p q h, agree1714 p q h]
theorem nonnegative6058 (p : Pattern) : 0 ≤ d6058 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1714 p)
def d6059 (p : Pattern) : Int := if p 182 then d6058 p else d6044 p
theorem agree6059 (p q : Pattern) (h : Agree support p q) : d6059 p = d6059 q := by
  simp only [d6059, h 182 (by decide), agree6058 p q h, agree6044 p q h]
theorem nonnegative6059 (p : Pattern) : 0 ≤ d6059 p :=
  nonnegative_ite (p 182) (nonnegative6058 p) (nonnegative6044 p)
def d6060 (p : Pattern) : Int := if p 204 then d12 p else d1722 p
theorem agree6060 (p q : Pattern) (h : Agree support p q) : d6060 p = d6060 q := by
  simp only [d6060, h 204 (by decide), agree12 p q h, agree1722 p q h]
theorem nonnegative6060 (p : Pattern) : 0 ≤ d6060 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1722 p)
def d6061 (p : Pattern) : Int := if p 182 then d6060 p else d6044 p
theorem agree6061 (p q : Pattern) (h : Agree support p q) : d6061 p = d6061 q := by
  simp only [d6061, h 182 (by decide), agree6060 p q h, agree6044 p q h]
theorem nonnegative6061 (p : Pattern) : 0 ≤ d6061 p :=
  nonnegative_ite (p 182) (nonnegative6060 p) (nonnegative6044 p)
def d6062 (p : Pattern) : Int := if p 163 then d6061 p else d6059 p
theorem agree6062 (p q : Pattern) (h : Agree support p q) : d6062 p = d6062 q := by
  simp only [d6062, h 163 (by decide), agree6061 p q h, agree6059 p q h]
theorem nonnegative6062 (p : Pattern) : 0 ≤ d6062 p :=
  nonnegative_ite (p 163) (nonnegative6061 p) (nonnegative6059 p)
def d6063 (p : Pattern) : Int := if p 204 then d12 p else d327 p
theorem agree6063 (p q : Pattern) (h : Agree support p q) : d6063 p = d6063 q := by
  simp only [d6063, h 204 (by decide), agree12 p q h, agree327 p q h]
theorem nonnegative6063 (p : Pattern) : 0 ≤ d6063 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative327 p)
def d6064 (p : Pattern) : Int := if p 182 then d6063 p else d6044 p
theorem agree6064 (p q : Pattern) (h : Agree support p q) : d6064 p = d6064 q := by
  simp only [d6064, h 182 (by decide), agree6063 p q h, agree6044 p q h]
theorem nonnegative6064 (p : Pattern) : 0 ≤ d6064 p :=
  nonnegative_ite (p 182) (nonnegative6063 p) (nonnegative6044 p)
def d6065 (p : Pattern) : Int := if p 182 then d12 p else d6047 p
theorem agree6065 (p q : Pattern) (h : Agree support p q) : d6065 p = d6065 q := by
  simp only [d6065, h 182 (by decide), agree12 p q h, agree6047 p q h]
theorem nonnegative6065 (p : Pattern) : 0 ≤ d6065 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6047 p)
def d6066 (p : Pattern) : Int := if p 163 then d6065 p else d6064 p
theorem agree6066 (p q : Pattern) (h : Agree support p q) : d6066 p = d6066 q := by
  simp only [d6066, h 163 (by decide), agree6065 p q h, agree6064 p q h]
theorem nonnegative6066 (p : Pattern) : 0 ≤ d6066 p :=
  nonnegative_ite (p 163) (nonnegative6065 p) (nonnegative6064 p)
def d6067 (p : Pattern) : Int := if p 162 then d6066 p else d6062 p
theorem agree6067 (p q : Pattern) (h : Agree support p q) : d6067 p = d6067 q := by
  simp only [d6067, h 162 (by decide), agree6066 p q h, agree6062 p q h]
theorem nonnegative6067 (p : Pattern) : 0 ≤ d6067 p :=
  nonnegative_ite (p 162) (nonnegative6066 p) (nonnegative6062 p)
def d6068 (p : Pattern) : Int := if p 182 then d12 p else d6044 p
theorem agree6068 (p q : Pattern) (h : Agree support p q) : d6068 p = d6068 q := by
  simp only [d6068, h 182 (by decide), agree12 p q h, agree6044 p q h]
theorem nonnegative6068 (p : Pattern) : 0 ≤ d6068 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6044 p)
def d6069 (p : Pattern) : Int := if p 163 then d6065 p else d6068 p
theorem agree6069 (p q : Pattern) (h : Agree support p q) : d6069 p = d6069 q := by
  simp only [d6069, h 163 (by decide), agree6065 p q h, agree6068 p q h]
theorem nonnegative6069 (p : Pattern) : 0 ≤ d6069 p :=
  nonnegative_ite (p 163) (nonnegative6065 p) (nonnegative6068 p)
def d6070 (p : Pattern) : Int := if p 182 then d12 p else d6052 p
theorem agree6070 (p q : Pattern) (h : Agree support p q) : d6070 p = d6070 q := by
  simp only [d6070, h 182 (by decide), agree12 p q h, agree6052 p q h]
theorem nonnegative6070 (p : Pattern) : 0 ≤ d6070 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6052 p)
def d6071 (p : Pattern) : Int := if p 163 then d12 p else d6070 p
theorem agree6071 (p q : Pattern) (h : Agree support p q) : d6071 p = d6071 q := by
  simp only [d6071, h 163 (by decide), agree12 p q h, agree6070 p q h]
theorem nonnegative6071 (p : Pattern) : 0 ≤ d6071 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6070 p)
def d6072 (p : Pattern) : Int := if p 162 then d6071 p else d6069 p
theorem agree6072 (p q : Pattern) (h : Agree support p q) : d6072 p = d6072 q := by
  simp only [d6072, h 162 (by decide), agree6071 p q h, agree6069 p q h]
theorem nonnegative6072 (p : Pattern) : 0 ≤ d6072 p :=
  nonnegative_ite (p 162) (nonnegative6071 p) (nonnegative6069 p)
def d6073 (p : Pattern) : Int := if p 161 then d6072 p else d6067 p
theorem agree6073 (p q : Pattern) (h : Agree support p q) : d6073 p = d6073 q := by
  simp only [d6073, h 161 (by decide), agree6072 p q h, agree6067 p q h]
theorem nonnegative6073 (p : Pattern) : 0 ≤ d6073 p :=
  nonnegative_ite (p 161) (nonnegative6072 p) (nonnegative6067 p)
def d6074 (p : Pattern) : Int := if p 160 then d6073 p else d6057 p
theorem agree6074 (p q : Pattern) (h : Agree support p q) : d6074 p = d6074 q := by
  simp only [d6074, h 160 (by decide), agree6073 p q h, agree6057 p q h]
theorem nonnegative6074 (p : Pattern) : 0 ≤ d6074 p :=
  nonnegative_ite (p 160) (nonnegative6073 p) (nonnegative6057 p)
def d6075 (p : Pattern) : Int := if p 204 then d1714 p else d31 p
theorem agree6075 (p q : Pattern) (h : Agree support p q) : d6075 p = d6075 q := by
  simp only [d6075, h 204 (by decide), agree1714 p q h, agree31 p q h]
theorem nonnegative6075 (p : Pattern) : 0 ≤ d6075 p :=
  nonnegative_ite (p 204) (nonnegative1714 p) (nonnegative31 p)
def d6076 (p : Pattern) : Int := if p 204 then d12 p else d1743 p
theorem agree6076 (p q : Pattern) (h : Agree support p q) : d6076 p = d6076 q := by
  simp only [d6076, h 204 (by decide), agree12 p q h, agree1743 p q h]
theorem nonnegative6076 (p : Pattern) : 0 ≤ d6076 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1743 p)
def d6077 (p : Pattern) : Int := if p 182 then d6076 p else d6075 p
theorem agree6077 (p q : Pattern) (h : Agree support p q) : d6077 p = d6077 q := by
  simp only [d6077, h 182 (by decide), agree6076 p q h, agree6075 p q h]
theorem nonnegative6077 (p : Pattern) : 0 ≤ d6077 p :=
  nonnegative_ite (p 182) (nonnegative6076 p) (nonnegative6075 p)
def d6078 (p : Pattern) : Int := if p 163 then d6077 p else d6046 p
theorem agree6078 (p q : Pattern) (h : Agree support p q) : d6078 p = d6078 q := by
  simp only [d6078, h 163 (by decide), agree6077 p q h, agree6046 p q h]
theorem nonnegative6078 (p : Pattern) : 0 ≤ d6078 p :=
  nonnegative_ite (p 163) (nonnegative6077 p) (nonnegative6046 p)
def d6079 (p : Pattern) : Int := if p 163 then d6054 p else d6049 p
theorem agree6079 (p q : Pattern) (h : Agree support p q) : d6079 p = d6079 q := by
  simp only [d6079, h 163 (by decide), agree6054 p q h, agree6049 p q h]
theorem nonnegative6079 (p : Pattern) : 0 ≤ d6079 p :=
  nonnegative_ite (p 163) (nonnegative6054 p) (nonnegative6049 p)
def d6080 (p : Pattern) : Int := if p 162 then d6079 p else d6078 p
theorem agree6080 (p q : Pattern) (h : Agree support p q) : d6080 p = d6080 q := by
  simp only [d6080, h 162 (by decide), agree6079 p q h, agree6078 p q h]
theorem nonnegative6080 (p : Pattern) : 0 ≤ d6080 p :=
  nonnegative_ite (p 162) (nonnegative6079 p) (nonnegative6078 p)
def d6081 (p : Pattern) : Int := if p 204 then d329 p else d58 p
theorem agree6081 (p q : Pattern) (h : Agree support p q) : d6081 p = d6081 q := by
  simp only [d6081, h 204 (by decide), agree329 p q h, agree58 p q h]
theorem nonnegative6081 (p : Pattern) : 0 ≤ d6081 p :=
  nonnegative_ite (p 204) (nonnegative329 p) (nonnegative58 p)
def d6082 (p : Pattern) : Int := if p 204 then d12 p else d329 p
theorem agree6082 (p q : Pattern) (h : Agree support p q) : d6082 p = d6082 q := by
  simp only [d6082, h 204 (by decide), agree12 p q h, agree329 p q h]
theorem nonnegative6082 (p : Pattern) : 0 ≤ d6082 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative329 p)
def d6083 (p : Pattern) : Int := if p 182 then d6082 p else d6081 p
theorem agree6083 (p q : Pattern) (h : Agree support p q) : d6083 p = d6083 q := by
  simp only [d6083, h 182 (by decide), agree6082 p q h, agree6081 p q h]
theorem nonnegative6083 (p : Pattern) : 0 ≤ d6083 p :=
  nonnegative_ite (p 182) (nonnegative6082 p) (nonnegative6081 p)
def d6084 (p : Pattern) : Int := if p 163 then d6083 p else d6049 p
theorem agree6084 (p q : Pattern) (h : Agree support p q) : d6084 p = d6084 q := by
  simp only [d6084, h 163 (by decide), agree6083 p q h, agree6049 p q h]
theorem nonnegative6084 (p : Pattern) : 0 ≤ d6084 p :=
  nonnegative_ite (p 163) (nonnegative6083 p) (nonnegative6049 p)
def d6085 (p : Pattern) : Int := if p 204 then d327 p else d40 p
theorem agree6085 (p q : Pattern) (h : Agree support p q) : d6085 p = d6085 q := by
  simp only [d6085, h 204 (by decide), agree327 p q h, agree40 p q h]
theorem nonnegative6085 (p : Pattern) : 0 ≤ d6085 p :=
  nonnegative_ite (p 204) (nonnegative327 p) (nonnegative40 p)
def d6086 (p : Pattern) : Int := if p 182 then d6063 p else d6085 p
theorem agree6086 (p q : Pattern) (h : Agree support p q) : d6086 p = d6086 q := by
  simp only [d6086, h 182 (by decide), agree6063 p q h, agree6085 p q h]
theorem nonnegative6086 (p : Pattern) : 0 ≤ d6086 p :=
  nonnegative_ite (p 182) (nonnegative6063 p) (nonnegative6085 p)
def d6087 (p : Pattern) : Int := if p 163 then d12 p else d6086 p
theorem agree6087 (p q : Pattern) (h : Agree support p q) : d6087 p = d6087 q := by
  simp only [d6087, h 163 (by decide), agree12 p q h, agree6086 p q h]
theorem nonnegative6087 (p : Pattern) : 0 ≤ d6087 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6086 p)
def d6088 (p : Pattern) : Int := if p 162 then d6087 p else d6084 p
theorem agree6088 (p q : Pattern) (h : Agree support p q) : d6088 p = d6088 q := by
  simp only [d6088, h 162 (by decide), agree6087 p q h, agree6084 p q h]
theorem nonnegative6088 (p : Pattern) : 0 ≤ d6088 p :=
  nonnegative_ite (p 162) (nonnegative6087 p) (nonnegative6084 p)
def d6089 (p : Pattern) : Int := if p 161 then d6088 p else d6080 p
theorem agree6089 (p q : Pattern) (h : Agree support p q) : d6089 p = d6089 q := by
  simp only [d6089, h 161 (by decide), agree6088 p q h, agree6080 p q h]
theorem nonnegative6089 (p : Pattern) : 0 ≤ d6089 p :=
  nonnegative_ite (p 161) (nonnegative6088 p) (nonnegative6080 p)
def d6090 (p : Pattern) : Int := if p 182 then d12 p else d6075 p
theorem agree6090 (p q : Pattern) (h : Agree support p q) : d6090 p = d6090 q := by
  simp only [d6090, h 182 (by decide), agree12 p q h, agree6075 p q h]
theorem nonnegative6090 (p : Pattern) : 0 ≤ d6090 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6075 p)
def d6091 (p : Pattern) : Int := if p 163 then d6090 p else d6061 p
theorem agree6091 (p q : Pattern) (h : Agree support p q) : d6091 p = d6091 q := by
  simp only [d6091, h 163 (by decide), agree6090 p q h, agree6061 p q h]
theorem nonnegative6091 (p : Pattern) : 0 ≤ d6091 p :=
  nonnegative_ite (p 163) (nonnegative6090 p) (nonnegative6061 p)
def d6092 (p : Pattern) : Int := if p 163 then d6070 p else d6065 p
theorem agree6092 (p q : Pattern) (h : Agree support p q) : d6092 p = d6092 q := by
  simp only [d6092, h 163 (by decide), agree6070 p q h, agree6065 p q h]
theorem nonnegative6092 (p : Pattern) : 0 ≤ d6092 p :=
  nonnegative_ite (p 163) (nonnegative6070 p) (nonnegative6065 p)
def d6093 (p : Pattern) : Int := if p 162 then d6092 p else d6091 p
theorem agree6093 (p q : Pattern) (h : Agree support p q) : d6093 p = d6093 q := by
  simp only [d6093, h 162 (by decide), agree6092 p q h, agree6091 p q h]
theorem nonnegative6093 (p : Pattern) : 0 ≤ d6093 p :=
  nonnegative_ite (p 162) (nonnegative6092 p) (nonnegative6091 p)
def d6094 (p : Pattern) : Int := if p 182 then d12 p else d6081 p
theorem agree6094 (p q : Pattern) (h : Agree support p q) : d6094 p = d6094 q := by
  simp only [d6094, h 182 (by decide), agree12 p q h, agree6081 p q h]
theorem nonnegative6094 (p : Pattern) : 0 ≤ d6094 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6081 p)
def d6095 (p : Pattern) : Int := if p 163 then d6094 p else d6065 p
theorem agree6095 (p q : Pattern) (h : Agree support p q) : d6095 p = d6095 q := by
  simp only [d6095, h 163 (by decide), agree6094 p q h, agree6065 p q h]
theorem nonnegative6095 (p : Pattern) : 0 ≤ d6095 p :=
  nonnegative_ite (p 163) (nonnegative6094 p) (nonnegative6065 p)
def d6096 (p : Pattern) : Int := if p 182 then d12 p else d6085 p
theorem agree6096 (p q : Pattern) (h : Agree support p q) : d6096 p = d6096 q := by
  simp only [d6096, h 182 (by decide), agree12 p q h, agree6085 p q h]
theorem nonnegative6096 (p : Pattern) : 0 ≤ d6096 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6085 p)
def d6097 (p : Pattern) : Int := if p 163 then d12 p else d6096 p
theorem agree6097 (p q : Pattern) (h : Agree support p q) : d6097 p = d6097 q := by
  simp only [d6097, h 163 (by decide), agree12 p q h, agree6096 p q h]
theorem nonnegative6097 (p : Pattern) : 0 ≤ d6097 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6096 p)
def d6098 (p : Pattern) : Int := if p 162 then d6097 p else d6095 p
theorem agree6098 (p q : Pattern) (h : Agree support p q) : d6098 p = d6098 q := by
  simp only [d6098, h 162 (by decide), agree6097 p q h, agree6095 p q h]
theorem nonnegative6098 (p : Pattern) : 0 ≤ d6098 p :=
  nonnegative_ite (p 162) (nonnegative6097 p) (nonnegative6095 p)
def d6099 (p : Pattern) : Int := if p 161 then d6098 p else d6093 p
theorem agree6099 (p q : Pattern) (h : Agree support p q) : d6099 p = d6099 q := by
  simp only [d6099, h 161 (by decide), agree6098 p q h, agree6093 p q h]
theorem nonnegative6099 (p : Pattern) : 0 ≤ d6099 p :=
  nonnegative_ite (p 161) (nonnegative6098 p) (nonnegative6093 p)
def d6100 (p : Pattern) : Int := if p 160 then d6099 p else d6089 p
theorem agree6100 (p q : Pattern) (h : Agree support p q) : d6100 p = d6100 q := by
  simp only [d6100, h 160 (by decide), agree6099 p q h, agree6089 p q h]
theorem nonnegative6100 (p : Pattern) : 0 ≤ d6100 p :=
  nonnegative_ite (p 160) (nonnegative6099 p) (nonnegative6089 p)
def d6101 (p : Pattern) : Int := if p 141 then d6100 p else d6074 p
theorem agree6101 (p q : Pattern) (h : Agree support p q) : d6101 p = d6101 q := by
  simp only [d6101, h 141 (by decide), agree6100 p q h, agree6074 p q h]
theorem nonnegative6101 (p : Pattern) : 0 ≤ d6101 p :=
  nonnegative_ite (p 141) (nonnegative6100 p) (nonnegative6074 p)
def d6102 (p : Pattern) : Int := if p 204 then d12 p else d1770 p
theorem agree6102 (p q : Pattern) (h : Agree support p q) : d6102 p = d6102 q := by
  simp only [d6102, h 204 (by decide), agree12 p q h, agree1770 p q h]
theorem nonnegative6102 (p : Pattern) : 0 ≤ d6102 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1770 p)
def d6103 (p : Pattern) : Int := if p 182 then d6102 p else d6044 p
theorem agree6103 (p q : Pattern) (h : Agree support p q) : d6103 p = d6103 q := by
  simp only [d6103, h 182 (by decide), agree6102 p q h, agree6044 p q h]
theorem nonnegative6103 (p : Pattern) : 0 ≤ d6103 p :=
  nonnegative_ite (p 182) (nonnegative6102 p) (nonnegative6044 p)
def d6104 (p : Pattern) : Int := if p 204 then d12 p else d1795 p
theorem agree6104 (p q : Pattern) (h : Agree support p q) : d6104 p = d6104 q := by
  simp only [d6104, h 204 (by decide), agree12 p q h, agree1795 p q h]
theorem nonnegative6104 (p : Pattern) : 0 ≤ d6104 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1795 p)
def d6105 (p : Pattern) : Int := if p 182 then d6104 p else d6047 p
theorem agree6105 (p q : Pattern) (h : Agree support p q) : d6105 p = d6105 q := by
  simp only [d6105, h 182 (by decide), agree6104 p q h, agree6047 p q h]
theorem nonnegative6105 (p : Pattern) : 0 ≤ d6105 p :=
  nonnegative_ite (p 182) (nonnegative6104 p) (nonnegative6047 p)
def d6106 (p : Pattern) : Int := if p 163 then d6105 p else d6103 p
theorem agree6106 (p q : Pattern) (h : Agree support p q) : d6106 p = d6106 q := by
  simp only [d6106, h 163 (by decide), agree6105 p q h, agree6103 p q h]
theorem nonnegative6106 (p : Pattern) : 0 ≤ d6106 p :=
  nonnegative_ite (p 163) (nonnegative6105 p) (nonnegative6103 p)
def d6107 (p : Pattern) : Int := if p 162 then d6106 p else d6103 p
theorem agree6107 (p q : Pattern) (h : Agree support p q) : d6107 p = d6107 q := by
  simp only [d6107, h 162 (by decide), agree6106 p q h, agree6103 p q h]
theorem nonnegative6107 (p : Pattern) : 0 ≤ d6107 p :=
  nonnegative_ite (p 162) (nonnegative6106 p) (nonnegative6103 p)
def d6108 (p : Pattern) : Int := if p 204 then d12 p else d356 p
theorem agree6108 (p q : Pattern) (h : Agree support p q) : d6108 p = d6108 q := by
  simp only [d6108, h 204 (by decide), agree12 p q h, agree356 p q h]
theorem nonnegative6108 (p : Pattern) : 0 ≤ d6108 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative356 p)
def d6109 (p : Pattern) : Int := if p 182 then d6108 p else d6052 p
theorem agree6109 (p q : Pattern) (h : Agree support p q) : d6109 p = d6109 q := by
  simp only [d6109, h 182 (by decide), agree6108 p q h, agree6052 p q h]
theorem nonnegative6109 (p : Pattern) : 0 ≤ d6109 p :=
  nonnegative_ite (p 182) (nonnegative6108 p) (nonnegative6052 p)
def d6110 (p : Pattern) : Int := if p 163 then d12 p else d6109 p
theorem agree6110 (p q : Pattern) (h : Agree support p q) : d6110 p = d6110 q := by
  simp only [d6110, h 163 (by decide), agree12 p q h, agree6109 p q h]
theorem nonnegative6110 (p : Pattern) : 0 ≤ d6110 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6109 p)
def d6111 (p : Pattern) : Int := if p 162 then d6110 p else d6106 p
theorem agree6111 (p q : Pattern) (h : Agree support p q) : d6111 p = d6111 q := by
  simp only [d6111, h 162 (by decide), agree6110 p q h, agree6106 p q h]
theorem nonnegative6111 (p : Pattern) : 0 ≤ d6111 p :=
  nonnegative_ite (p 162) (nonnegative6110 p) (nonnegative6106 p)
def d6112 (p : Pattern) : Int := if p 161 then d6111 p else d6107 p
theorem agree6112 (p q : Pattern) (h : Agree support p q) : d6112 p = d6112 q := by
  simp only [d6112, h 161 (by decide), agree6111 p q h, agree6107 p q h]
theorem nonnegative6112 (p : Pattern) : 0 ≤ d6112 p :=
  nonnegative_ite (p 161) (nonnegative6111 p) (nonnegative6107 p)
def d6113 (p : Pattern) : Int := if p 182 then d6058 p else d6075 p
theorem agree6113 (p q : Pattern) (h : Agree support p q) : d6113 p = d6113 q := by
  simp only [d6113, h 182 (by decide), agree6058 p q h, agree6075 p q h]
theorem nonnegative6113 (p : Pattern) : 0 ≤ d6113 p :=
  nonnegative_ite (p 182) (nonnegative6058 p) (nonnegative6075 p)
def d6114 (p : Pattern) : Int := if p 204 then d1722 p else d35 p
theorem agree6114 (p q : Pattern) (h : Agree support p q) : d6114 p = d6114 q := by
  simp only [d6114, h 204 (by decide), agree1722 p q h, agree35 p q h]
theorem nonnegative6114 (p : Pattern) : 0 ≤ d6114 p :=
  nonnegative_ite (p 204) (nonnegative1722 p) (nonnegative35 p)
def d6115 (p : Pattern) : Int := if p 182 then d6060 p else d6114 p
theorem agree6115 (p q : Pattern) (h : Agree support p q) : d6115 p = d6115 q := by
  simp only [d6115, h 182 (by decide), agree6060 p q h, agree6114 p q h]
theorem nonnegative6115 (p : Pattern) : 0 ≤ d6115 p :=
  nonnegative_ite (p 182) (nonnegative6060 p) (nonnegative6114 p)
def d6116 (p : Pattern) : Int := if p 163 then d6115 p else d6113 p
theorem agree6116 (p q : Pattern) (h : Agree support p q) : d6116 p = d6116 q := by
  simp only [d6116, h 163 (by decide), agree6115 p q h, agree6113 p q h]
theorem nonnegative6116 (p : Pattern) : 0 ≤ d6116 p :=
  nonnegative_ite (p 163) (nonnegative6115 p) (nonnegative6113 p)
def d6117 (p : Pattern) : Int := if p 162 then d6087 p else d6116 p
theorem agree6117 (p q : Pattern) (h : Agree support p q) : d6117 p = d6117 q := by
  simp only [d6117, h 162 (by decide), agree6087 p q h, agree6116 p q h]
theorem nonnegative6117 (p : Pattern) : 0 ≤ d6117 p :=
  nonnegative_ite (p 162) (nonnegative6087 p) (nonnegative6116 p)
def d6118 (p : Pattern) : Int := if p 161 then d12 p else d6117 p
theorem agree6118 (p q : Pattern) (h : Agree support p q) : d6118 p = d6118 q := by
  simp only [d6118, h 161 (by decide), agree12 p q h, agree6117 p q h]
theorem nonnegative6118 (p : Pattern) : 0 ≤ d6118 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6117 p)
def d6119 (p : Pattern) : Int := if p 160 then d6118 p else d6112 p
theorem agree6119 (p q : Pattern) (h : Agree support p q) : d6119 p = d6119 q := by
  simp only [d6119, h 160 (by decide), agree6118 p q h, agree6112 p q h]
theorem nonnegative6119 (p : Pattern) : 0 ≤ d6119 p :=
  nonnegative_ite (p 160) (nonnegative6118 p) (nonnegative6112 p)
end NetHack.Sokoban22Refined85
