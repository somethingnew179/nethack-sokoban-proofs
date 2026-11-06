/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes41
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5040 (p : Pattern) : Int := if p 163 then d12 p else d5029 p
theorem agree5040 (p q : Pattern) (h : Agree support p q) : d5040 p = d5040 q := by
  simp only [d5040, h 163 (by decide), agree12 p q h, agree5029 p q h]
theorem nonnegative5040 (p : Pattern) : 0 ≤ d5040 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5029 p)
def d5041 (p : Pattern) : Int := if p 162 then d12 p else d5040 p
theorem agree5041 (p q : Pattern) (h : Agree support p q) : d5041 p = d5041 q := by
  simp only [d5041, h 162 (by decide), agree12 p q h, agree5040 p q h]
theorem nonnegative5041 (p : Pattern) : 0 ≤ d5041 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5040 p)
def d5042 (p : Pattern) : Int := if p 161 then d12 p else d5041 p
theorem agree5042 (p q : Pattern) (h : Agree support p q) : d5042 p = d5042 q := by
  simp only [d5042, h 161 (by decide), agree12 p q h, agree5041 p q h]
theorem nonnegative5042 (p : Pattern) : 0 ≤ d5042 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5041 p)
def d5043 (p : Pattern) : Int := if p 160 then d5042 p else d5039 p
theorem agree5043 (p q : Pattern) (h : Agree support p q) : d5043 p = d5043 q := by
  simp only [d5043, h 160 (by decide), agree5042 p q h, agree5039 p q h]
theorem nonnegative5043 (p : Pattern) : 0 ≤ d5043 p :=
  nonnegative_ite (p 160) (nonnegative5042 p) (nonnegative5039 p)
def d5044 (p : Pattern) : Int := if p 141 then d5043 p else d5033 p
theorem agree5044 (p q : Pattern) (h : Agree support p q) : d5044 p = d5044 q := by
  simp only [d5044, h 141 (by decide), agree5043 p q h, agree5033 p q h]
theorem nonnegative5044 (p : Pattern) : 0 ≤ d5044 p :=
  nonnegative_ite (p 141) (nonnegative5043 p) (nonnegative5033 p)
def d5045 (p : Pattern) : Int := if p 138 then d5044 p else d5016 p
theorem agree5045 (p q : Pattern) (h : Agree support p q) : d5045 p = d5045 q := by
  simp only [d5045, h 138 (by decide), agree5044 p q h, agree5016 p q h]
theorem nonnegative5045 (p : Pattern) : 0 ≤ d5045 p :=
  nonnegative_ite (p 138) (nonnegative5044 p) (nonnegative5016 p)
def d5046 (p : Pattern) : Int := if p 163 then d5008 p else d5024 p
theorem agree5046 (p q : Pattern) (h : Agree support p q) : d5046 p = d5046 q := by
  simp only [d5046, h 163 (by decide), agree5008 p q h, agree5024 p q h]
theorem nonnegative5046 (p : Pattern) : 0 ≤ d5046 p :=
  nonnegative_ite (p 163) (nonnegative5008 p) (nonnegative5024 p)
def d5047 (p : Pattern) : Int := if p 162 then d5009 p else d5046 p
theorem agree5047 (p q : Pattern) (h : Agree support p q) : d5047 p = d5047 q := by
  simp only [d5047, h 162 (by decide), agree5009 p q h, agree5046 p q h]
theorem nonnegative5047 (p : Pattern) : 0 ≤ d5047 p :=
  nonnegative_ite (p 162) (nonnegative5009 p) (nonnegative5046 p)
def d5048 (p : Pattern) : Int := if p 162 then d12 p else d5009 p
theorem agree5048 (p q : Pattern) (h : Agree support p q) : d5048 p = d5048 q := by
  simp only [d5048, h 162 (by decide), agree12 p q h, agree5009 p q h]
theorem nonnegative5048 (p : Pattern) : 0 ≤ d5048 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5009 p)
def d5049 (p : Pattern) : Int := if p 161 then d5048 p else d5047 p
theorem agree5049 (p q : Pattern) (h : Agree support p q) : d5049 p = d5049 q := by
  simp only [d5049, h 161 (by decide), agree5048 p q h, agree5047 p q h]
theorem nonnegative5049 (p : Pattern) : 0 ≤ d5049 p :=
  nonnegative_ite (p 161) (nonnegative5048 p) (nonnegative5047 p)
def d5050 (p : Pattern) : Int := if p 161 then d12 p else d5048 p
theorem agree5050 (p q : Pattern) (h : Agree support p q) : d5050 p = d5050 q := by
  simp only [d5050, h 161 (by decide), agree12 p q h, agree5048 p q h]
theorem nonnegative5050 (p : Pattern) : 0 ≤ d5050 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5048 p)
def d5051 (p : Pattern) : Int := if p 160 then d5050 p else d5049 p
theorem agree5051 (p q : Pattern) (h : Agree support p q) : d5051 p = d5051 q := by
  simp only [d5051, h 160 (by decide), agree5050 p q h, agree5049 p q h]
theorem nonnegative5051 (p : Pattern) : 0 ≤ d5051 p :=
  nonnegative_ite (p 160) (nonnegative5050 p) (nonnegative5049 p)
def d5052 (p : Pattern) : Int := if p 160 then d12 p else d5050 p
theorem agree5052 (p q : Pattern) (h : Agree support p q) : d5052 p = d5052 q := by
  simp only [d5052, h 160 (by decide), agree12 p q h, agree5050 p q h]
theorem nonnegative5052 (p : Pattern) : 0 ≤ d5052 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5050 p)
def d5053 (p : Pattern) : Int := if p 141 then d5052 p else d5051 p
theorem agree5053 (p q : Pattern) (h : Agree support p q) : d5053 p = d5053 q := by
  simp only [d5053, h 141 (by decide), agree5052 p q h, agree5051 p q h]
theorem nonnegative5053 (p : Pattern) : 0 ≤ d5053 p :=
  nonnegative_ite (p 141) (nonnegative5052 p) (nonnegative5051 p)
def d5054 (p : Pattern) : Int := if p 138 then d5053 p else d5044 p
theorem agree5054 (p q : Pattern) (h : Agree support p q) : d5054 p = d5054 q := by
  simp only [d5054, h 138 (by decide), agree5053 p q h, agree5044 p q h]
theorem nonnegative5054 (p : Pattern) : 0 ≤ d5054 p :=
  nonnegative_ite (p 138) (nonnegative5053 p) (nonnegative5044 p)
def d5055 (p : Pattern) : Int := if p 116 then d5054 p else d5045 p
theorem agree5055 (p q : Pattern) (h : Agree support p q) : d5055 p = d5055 q := by
  simp only [d5055, h 116 (by decide), agree5054 p q h, agree5045 p q h]
theorem nonnegative5055 (p : Pattern) : 0 ≤ d5055 p :=
  nonnegative_ite (p 116) (nonnegative5054 p) (nonnegative5045 p)
def d5056 (p : Pattern) : Int := if p 138 then d12 p else d5044 p
theorem agree5056 (p q : Pattern) (h : Agree support p q) : d5056 p = d5056 q := by
  simp only [d5056, h 138 (by decide), agree12 p q h, agree5044 p q h]
theorem nonnegative5056 (p : Pattern) : 0 ≤ d5056 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5044 p)
def d5057 (p : Pattern) : Int := if p 116 then d5056 p else d5045 p
theorem agree5057 (p q : Pattern) (h : Agree support p q) : d5057 p = d5057 q := by
  simp only [d5057, h 116 (by decide), agree5056 p q h, agree5045 p q h]
theorem nonnegative5057 (p : Pattern) : 0 ≤ d5057 p :=
  nonnegative_ite (p 116) (nonnegative5056 p) (nonnegative5045 p)
def d5058 (p : Pattern) : Int := if p 115 then d5057 p else d5055 p
theorem agree5058 (p q : Pattern) (h : Agree support p q) : d5058 p = d5058 q := by
  simp only [d5058, h 115 (by decide), agree5057 p q h, agree5055 p q h]
theorem nonnegative5058 (p : Pattern) : 0 ≤ d5058 p :=
  nonnegative_ite (p 115) (nonnegative5057 p) (nonnegative5055 p)
def d5059 (p : Pattern) : Int := if p 182 then d1875 p else d103 p
theorem agree5059 (p q : Pattern) (h : Agree support p q) : d5059 p = d5059 q := by
  simp only [d5059, h 182 (by decide), agree1875 p q h, agree103 p q h]
theorem nonnegative5059 (p : Pattern) : 0 ≤ d5059 p :=
  nonnegative_ite (p 182) (nonnegative1875 p) (nonnegative103 p)
def d5060 (p : Pattern) : Int := if p 182 then d1883 p else d107 p
theorem agree5060 (p q : Pattern) (h : Agree support p q) : d5060 p = d5060 q := by
  simp only [d5060, h 182 (by decide), agree1883 p q h, agree107 p q h]
theorem nonnegative5060 (p : Pattern) : 0 ≤ d5060 p :=
  nonnegative_ite (p 182) (nonnegative1883 p) (nonnegative107 p)
def d5061 (p : Pattern) : Int := if p 163 then d5060 p else d5059 p
theorem agree5061 (p q : Pattern) (h : Agree support p q) : d5061 p = d5061 q := by
  simp only [d5061, h 163 (by decide), agree5060 p q h, agree5059 p q h]
theorem nonnegative5061 (p : Pattern) : 0 ≤ d5061 p :=
  nonnegative_ite (p 163) (nonnegative5060 p) (nonnegative5059 p)
def d5062 (p : Pattern) : Int := if p 162 then d5061 p else d5059 p
theorem agree5062 (p q : Pattern) (h : Agree support p q) : d5062 p = d5062 q := by
  simp only [d5062, h 162 (by decide), agree5061 p q h, agree5059 p q h]
theorem nonnegative5062 (p : Pattern) : 0 ≤ d5062 p :=
  nonnegative_ite (p 162) (nonnegative5061 p) (nonnegative5059 p)
def d5063 (p : Pattern) : Int := if p 163 then d12 p else d5006 p
theorem agree5063 (p q : Pattern) (h : Agree support p q) : d5063 p = d5063 q := by
  simp only [d5063, h 163 (by decide), agree12 p q h, agree5006 p q h]
theorem nonnegative5063 (p : Pattern) : 0 ≤ d5063 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5006 p)
def d5064 (p : Pattern) : Int := if p 162 then d5063 p else d5061 p
theorem agree5064 (p q : Pattern) (h : Agree support p q) : d5064 p = d5064 q := by
  simp only [d5064, h 162 (by decide), agree5063 p q h, agree5061 p q h]
theorem nonnegative5064 (p : Pattern) : 0 ≤ d5064 p :=
  nonnegative_ite (p 162) (nonnegative5063 p) (nonnegative5061 p)
def d5065 (p : Pattern) : Int := if p 161 then d5064 p else d5062 p
theorem agree5065 (p q : Pattern) (h : Agree support p q) : d5065 p = d5065 q := by
  simp only [d5065, h 161 (by decide), agree5064 p q h, agree5062 p q h]
theorem nonnegative5065 (p : Pattern) : 0 ≤ d5065 p :=
  nonnegative_ite (p 161) (nonnegative5064 p) (nonnegative5062 p)
def d5066 (p : Pattern) : Int := if p 182 then d1898 p else d103 p
theorem agree5066 (p q : Pattern) (h : Agree support p q) : d5066 p = d5066 q := by
  simp only [d5066, h 182 (by decide), agree1898 p q h, agree103 p q h]
theorem nonnegative5066 (p : Pattern) : 0 ≤ d5066 p :=
  nonnegative_ite (p 182) (nonnegative1898 p) (nonnegative103 p)
def d5067 (p : Pattern) : Int := if p 182 then d1905 p else d103 p
theorem agree5067 (p q : Pattern) (h : Agree support p q) : d5067 p = d5067 q := by
  simp only [d5067, h 182 (by decide), agree1905 p q h, agree103 p q h]
theorem nonnegative5067 (p : Pattern) : 0 ≤ d5067 p :=
  nonnegative_ite (p 182) (nonnegative1905 p) (nonnegative103 p)
def d5068 (p : Pattern) : Int := if p 163 then d5067 p else d5066 p
theorem agree5068 (p q : Pattern) (h : Agree support p q) : d5068 p = d5068 q := by
  simp only [d5068, h 163 (by decide), agree5067 p q h, agree5066 p q h]
theorem nonnegative5068 (p : Pattern) : 0 ≤ d5068 p :=
  nonnegative_ite (p 163) (nonnegative5067 p) (nonnegative5066 p)
def d5069 (p : Pattern) : Int := if p 162 then d126 p else d5068 p
theorem agree5069 (p q : Pattern) (h : Agree support p q) : d5069 p = d5069 q := by
  simp only [d5069, h 162 (by decide), agree126 p q h, agree5068 p q h]
theorem nonnegative5069 (p : Pattern) : 0 ≤ d5069 p :=
  nonnegative_ite (p 162) (nonnegative126 p) (nonnegative5068 p)
def d5070 (p : Pattern) : Int := if p 161 then d129 p else d5069 p
theorem agree5070 (p q : Pattern) (h : Agree support p q) : d5070 p = d5070 q := by
  simp only [d5070, h 161 (by decide), agree129 p q h, agree5069 p q h]
theorem nonnegative5070 (p : Pattern) : 0 ≤ d5070 p :=
  nonnegative_ite (p 161) (nonnegative129 p) (nonnegative5069 p)
def d5071 (p : Pattern) : Int := if p 160 then d5070 p else d5065 p
theorem agree5071 (p q : Pattern) (h : Agree support p q) : d5071 p = d5071 q := by
  simp only [d5071, h 160 (by decide), agree5070 p q h, agree5065 p q h]
theorem nonnegative5071 (p : Pattern) : 0 ≤ d5071 p :=
  nonnegative_ite (p 160) (nonnegative5070 p) (nonnegative5065 p)
def d5072 (p : Pattern) : Int := if p 182 then d1921 p else d116 p
theorem agree5072 (p q : Pattern) (h : Agree support p q) : d5072 p = d5072 q := by
  simp only [d5072, h 182 (by decide), agree1921 p q h, agree116 p q h]
theorem nonnegative5072 (p : Pattern) : 0 ≤ d5072 p :=
  nonnegative_ite (p 182) (nonnegative1921 p) (nonnegative116 p)
def d5073 (p : Pattern) : Int := if p 163 then d5072 p else d5059 p
theorem agree5073 (p q : Pattern) (h : Agree support p q) : d5073 p = d5073 q := by
  simp only [d5073, h 163 (by decide), agree5072 p q h, agree5059 p q h]
theorem nonnegative5073 (p : Pattern) : 0 ≤ d5073 p :=
  nonnegative_ite (p 163) (nonnegative5072 p) (nonnegative5059 p)
def d5074 (p : Pattern) : Int := if p 163 then d5006 p else d5060 p
theorem agree5074 (p q : Pattern) (h : Agree support p q) : d5074 p = d5074 q := by
  simp only [d5074, h 163 (by decide), agree5006 p q h, agree5060 p q h]
theorem nonnegative5074 (p : Pattern) : 0 ≤ d5074 p :=
  nonnegative_ite (p 163) (nonnegative5006 p) (nonnegative5060 p)
def d5075 (p : Pattern) : Int := if p 162 then d5074 p else d5073 p
theorem agree5075 (p q : Pattern) (h : Agree support p q) : d5075 p = d5075 q := by
  simp only [d5075, h 162 (by decide), agree5074 p q h, agree5073 p q h]
theorem nonnegative5075 (p : Pattern) : 0 ≤ d5075 p :=
  nonnegative_ite (p 162) (nonnegative5074 p) (nonnegative5073 p)
def d5076 (p : Pattern) : Int := if p 163 then d5008 p else d5060 p
theorem agree5076 (p q : Pattern) (h : Agree support p q) : d5076 p = d5076 q := by
  simp only [d5076, h 163 (by decide), agree5008 p q h, agree5060 p q h]
theorem nonnegative5076 (p : Pattern) : 0 ≤ d5076 p :=
  nonnegative_ite (p 163) (nonnegative5008 p) (nonnegative5060 p)
def d5077 (p : Pattern) : Int := if p 162 then d12 p else d5076 p
theorem agree5077 (p q : Pattern) (h : Agree support p q) : d5077 p = d5077 q := by
  simp only [d5077, h 162 (by decide), agree12 p q h, agree5076 p q h]
theorem nonnegative5077 (p : Pattern) : 0 ≤ d5077 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5076 p)
def d5078 (p : Pattern) : Int := if p 161 then d5077 p else d5075 p
theorem agree5078 (p q : Pattern) (h : Agree support p q) : d5078 p = d5078 q := by
  simp only [d5078, h 161 (by decide), agree5077 p q h, agree5075 p q h]
theorem nonnegative5078 (p : Pattern) : 0 ≤ d5078 p :=
  nonnegative_ite (p 161) (nonnegative5077 p) (nonnegative5075 p)
def d5079 (p : Pattern) : Int := if p 163 then d139 p else d5067 p
theorem agree5079 (p q : Pattern) (h : Agree support p q) : d5079 p = d5079 q := by
  simp only [d5079, h 163 (by decide), agree139 p q h, agree5067 p q h]
theorem nonnegative5079 (p : Pattern) : 0 ≤ d5079 p :=
  nonnegative_ite (p 163) (nonnegative139 p) (nonnegative5067 p)
def d5080 (p : Pattern) : Int := if p 162 then d141 p else d5079 p
theorem agree5080 (p q : Pattern) (h : Agree support p q) : d5080 p = d5080 q := by
  simp only [d5080, h 162 (by decide), agree141 p q h, agree5079 p q h]
theorem nonnegative5080 (p : Pattern) : 0 ≤ d5080 p :=
  nonnegative_ite (p 162) (nonnegative141 p) (nonnegative5079 p)
def d5081 (p : Pattern) : Int := if p 161 then d144 p else d5080 p
theorem agree5081 (p q : Pattern) (h : Agree support p q) : d5081 p = d5081 q := by
  simp only [d5081, h 161 (by decide), agree144 p q h, agree5080 p q h]
theorem nonnegative5081 (p : Pattern) : 0 ≤ d5081 p :=
  nonnegative_ite (p 161) (nonnegative144 p) (nonnegative5080 p)
def d5082 (p : Pattern) : Int := if p 160 then d5081 p else d5078 p
theorem agree5082 (p q : Pattern) (h : Agree support p q) : d5082 p = d5082 q := by
  simp only [d5082, h 160 (by decide), agree5081 p q h, agree5078 p q h]
theorem nonnegative5082 (p : Pattern) : 0 ≤ d5082 p :=
  nonnegative_ite (p 160) (nonnegative5081 p) (nonnegative5078 p)
def d5083 (p : Pattern) : Int := if p 141 then d5082 p else d5071 p
theorem agree5083 (p q : Pattern) (h : Agree support p q) : d5083 p = d5083 q := by
  simp only [d5083, h 141 (by decide), agree5082 p q h, agree5071 p q h]
theorem nonnegative5083 (p : Pattern) : 0 ≤ d5083 p :=
  nonnegative_ite (p 141) (nonnegative5082 p) (nonnegative5071 p)
def d5084 (p : Pattern) : Int := if p 182 then d1942 p else d103 p
theorem agree5084 (p q : Pattern) (h : Agree support p q) : d5084 p = d5084 q := by
  simp only [d5084, h 182 (by decide), agree1942 p q h, agree103 p q h]
theorem nonnegative5084 (p : Pattern) : 0 ≤ d5084 p :=
  nonnegative_ite (p 182) (nonnegative1942 p) (nonnegative103 p)
def d5085 (p : Pattern) : Int := if p 182 then d1951 p else d103 p
theorem agree5085 (p q : Pattern) (h : Agree support p q) : d5085 p = d5085 q := by
  simp only [d5085, h 182 (by decide), agree1951 p q h, agree103 p q h]
theorem nonnegative5085 (p : Pattern) : 0 ≤ d5085 p :=
  nonnegative_ite (p 182) (nonnegative1951 p) (nonnegative103 p)
def d5086 (p : Pattern) : Int := if p 163 then d5085 p else d5084 p
theorem agree5086 (p q : Pattern) (h : Agree support p q) : d5086 p = d5086 q := by
  simp only [d5086, h 163 (by decide), agree5085 p q h, agree5084 p q h]
theorem nonnegative5086 (p : Pattern) : 0 ≤ d5086 p :=
  nonnegative_ite (p 163) (nonnegative5085 p) (nonnegative5084 p)
def d5087 (p : Pattern) : Int := if p 182 then d1957 p else d103 p
theorem agree5087 (p q : Pattern) (h : Agree support p q) : d5087 p = d5087 q := by
  simp only [d5087, h 182 (by decide), agree1957 p q h, agree103 p q h]
theorem nonnegative5087 (p : Pattern) : 0 ≤ d5087 p :=
  nonnegative_ite (p 182) (nonnegative1957 p) (nonnegative103 p)
def d5088 (p : Pattern) : Int := if p 182 then d1966 p else d107 p
theorem agree5088 (p q : Pattern) (h : Agree support p q) : d5088 p = d5088 q := by
  simp only [d5088, h 182 (by decide), agree1966 p q h, agree107 p q h]
theorem nonnegative5088 (p : Pattern) : 0 ≤ d5088 p :=
  nonnegative_ite (p 182) (nonnegative1966 p) (nonnegative107 p)
def d5089 (p : Pattern) : Int := if p 163 then d5088 p else d5087 p
theorem agree5089 (p q : Pattern) (h : Agree support p q) : d5089 p = d5089 q := by
  simp only [d5089, h 163 (by decide), agree5088 p q h, agree5087 p q h]
theorem nonnegative5089 (p : Pattern) : 0 ≤ d5089 p :=
  nonnegative_ite (p 163) (nonnegative5088 p) (nonnegative5087 p)
def d5090 (p : Pattern) : Int := if p 162 then d5089 p else d5086 p
theorem agree5090 (p q : Pattern) (h : Agree support p q) : d5090 p = d5090 q := by
  simp only [d5090, h 162 (by decide), agree5089 p q h, agree5086 p q h]
theorem nonnegative5090 (p : Pattern) : 0 ≤ d5090 p :=
  nonnegative_ite (p 162) (nonnegative5089 p) (nonnegative5086 p)
def d5091 (p : Pattern) : Int := if p 162 then d5063 p else d5089 p
theorem agree5091 (p q : Pattern) (h : Agree support p q) : d5091 p = d5091 q := by
  simp only [d5091, h 162 (by decide), agree5063 p q h, agree5089 p q h]
theorem nonnegative5091 (p : Pattern) : 0 ≤ d5091 p :=
  nonnegative_ite (p 162) (nonnegative5063 p) (nonnegative5089 p)
def d5092 (p : Pattern) : Int := if p 161 then d5091 p else d5090 p
theorem agree5092 (p q : Pattern) (h : Agree support p q) : d5092 p = d5092 q := by
  simp only [d5092, h 161 (by decide), agree5091 p q h, agree5090 p q h]
theorem nonnegative5092 (p : Pattern) : 0 ≤ d5092 p :=
  nonnegative_ite (p 161) (nonnegative5091 p) (nonnegative5090 p)
def d5093 (p : Pattern) : Int := if p 182 then d1898 p else d116 p
theorem agree5093 (p q : Pattern) (h : Agree support p q) : d5093 p = d5093 q := by
  simp only [d5093, h 182 (by decide), agree1898 p q h, agree116 p q h]
theorem nonnegative5093 (p : Pattern) : 0 ≤ d5093 p :=
  nonnegative_ite (p 182) (nonnegative1898 p) (nonnegative116 p)
def d5094 (p : Pattern) : Int := if p 182 then d1905 p else d120 p
theorem agree5094 (p q : Pattern) (h : Agree support p q) : d5094 p = d5094 q := by
  simp only [d5094, h 182 (by decide), agree1905 p q h, agree120 p q h]
theorem nonnegative5094 (p : Pattern) : 0 ≤ d5094 p :=
  nonnegative_ite (p 182) (nonnegative1905 p) (nonnegative120 p)
def d5095 (p : Pattern) : Int := if p 163 then d5094 p else d5093 p
theorem agree5095 (p q : Pattern) (h : Agree support p q) : d5095 p = d5095 q := by
  simp only [d5095, h 163 (by decide), agree5094 p q h, agree5093 p q h]
theorem nonnegative5095 (p : Pattern) : 0 ≤ d5095 p :=
  nonnegative_ite (p 163) (nonnegative5094 p) (nonnegative5093 p)
def d5096 (p : Pattern) : Int := if p 162 then d12 p else d5095 p
theorem agree5096 (p q : Pattern) (h : Agree support p q) : d5096 p = d5096 q := by
  simp only [d5096, h 162 (by decide), agree12 p q h, agree5095 p q h]
theorem nonnegative5096 (p : Pattern) : 0 ≤ d5096 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5095 p)
def d5097 (p : Pattern) : Int := if p 161 then d12 p else d5096 p
theorem agree5097 (p q : Pattern) (h : Agree support p q) : d5097 p = d5097 q := by
  simp only [d5097, h 161 (by decide), agree12 p q h, agree5096 p q h]
theorem nonnegative5097 (p : Pattern) : 0 ≤ d5097 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5096 p)
def d5098 (p : Pattern) : Int := if p 160 then d5097 p else d5092 p
theorem agree5098 (p q : Pattern) (h : Agree support p q) : d5098 p = d5098 q := by
  simp only [d5098, h 160 (by decide), agree5097 p q h, agree5092 p q h]
theorem nonnegative5098 (p : Pattern) : 0 ≤ d5098 p :=
  nonnegative_ite (p 160) (nonnegative5097 p) (nonnegative5092 p)
def d5099 (p : Pattern) : Int := if p 163 then d5093 p else d5085 p
theorem agree5099 (p q : Pattern) (h : Agree support p q) : d5099 p = d5099 q := by
  simp only [d5099, h 163 (by decide), agree5093 p q h, agree5085 p q h]
theorem nonnegative5099 (p : Pattern) : 0 ≤ d5099 p :=
  nonnegative_ite (p 163) (nonnegative5093 p) (nonnegative5085 p)
def d5100 (p : Pattern) : Int := if p 163 then d5006 p else d5088 p
theorem agree5100 (p q : Pattern) (h : Agree support p q) : d5100 p = d5100 q := by
  simp only [d5100, h 163 (by decide), agree5006 p q h, agree5088 p q h]
theorem nonnegative5100 (p : Pattern) : 0 ≤ d5100 p :=
  nonnegative_ite (p 163) (nonnegative5006 p) (nonnegative5088 p)
def d5101 (p : Pattern) : Int := if p 162 then d5100 p else d5099 p
theorem agree5101 (p q : Pattern) (h : Agree support p q) : d5101 p = d5101 q := by
  simp only [d5101, h 162 (by decide), agree5100 p q h, agree5099 p q h]
theorem nonnegative5101 (p : Pattern) : 0 ≤ d5101 p :=
  nonnegative_ite (p 162) (nonnegative5100 p) (nonnegative5099 p)
def d5102 (p : Pattern) : Int := if p 163 then d5008 p else d5088 p
theorem agree5102 (p q : Pattern) (h : Agree support p q) : d5102 p = d5102 q := by
  simp only [d5102, h 163 (by decide), agree5008 p q h, agree5088 p q h]
theorem nonnegative5102 (p : Pattern) : 0 ≤ d5102 p :=
  nonnegative_ite (p 163) (nonnegative5008 p) (nonnegative5088 p)
def d5103 (p : Pattern) : Int := if p 162 then d12 p else d5102 p
theorem agree5103 (p q : Pattern) (h : Agree support p q) : d5103 p = d5103 q := by
  simp only [d5103, h 162 (by decide), agree12 p q h, agree5102 p q h]
theorem nonnegative5103 (p : Pattern) : 0 ≤ d5103 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5102 p)
def d5104 (p : Pattern) : Int := if p 161 then d5103 p else d5101 p
theorem agree5104 (p q : Pattern) (h : Agree support p q) : d5104 p = d5104 q := by
  simp only [d5104, h 161 (by decide), agree5103 p q h, agree5101 p q h]
theorem nonnegative5104 (p : Pattern) : 0 ≤ d5104 p :=
  nonnegative_ite (p 161) (nonnegative5103 p) (nonnegative5101 p)
def d5105 (p : Pattern) : Int := if p 163 then d12 p else d5094 p
theorem agree5105 (p q : Pattern) (h : Agree support p q) : d5105 p = d5105 q := by
  simp only [d5105, h 163 (by decide), agree12 p q h, agree5094 p q h]
theorem nonnegative5105 (p : Pattern) : 0 ≤ d5105 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5094 p)
def d5106 (p : Pattern) : Int := if p 162 then d12 p else d5105 p
theorem agree5106 (p q : Pattern) (h : Agree support p q) : d5106 p = d5106 q := by
  simp only [d5106, h 162 (by decide), agree12 p q h, agree5105 p q h]
theorem nonnegative5106 (p : Pattern) : 0 ≤ d5106 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5105 p)
def d5107 (p : Pattern) : Int := if p 161 then d12 p else d5106 p
theorem agree5107 (p q : Pattern) (h : Agree support p q) : d5107 p = d5107 q := by
  simp only [d5107, h 161 (by decide), agree12 p q h, agree5106 p q h]
theorem nonnegative5107 (p : Pattern) : 0 ≤ d5107 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5106 p)
def d5108 (p : Pattern) : Int := if p 160 then d5107 p else d5104 p
theorem agree5108 (p q : Pattern) (h : Agree support p q) : d5108 p = d5108 q := by
  simp only [d5108, h 160 (by decide), agree5107 p q h, agree5104 p q h]
theorem nonnegative5108 (p : Pattern) : 0 ≤ d5108 p :=
  nonnegative_ite (p 160) (nonnegative5107 p) (nonnegative5104 p)
def d5109 (p : Pattern) : Int := if p 141 then d5108 p else d5098 p
theorem agree5109 (p q : Pattern) (h : Agree support p q) : d5109 p = d5109 q := by
  simp only [d5109, h 141 (by decide), agree5108 p q h, agree5098 p q h]
theorem nonnegative5109 (p : Pattern) : 0 ≤ d5109 p :=
  nonnegative_ite (p 141) (nonnegative5108 p) (nonnegative5098 p)
def d5110 (p : Pattern) : Int := if p 138 then d5109 p else d5083 p
theorem agree5110 (p q : Pattern) (h : Agree support p q) : d5110 p = d5110 q := by
  simp only [d5110, h 138 (by decide), agree5109 p q h, agree5083 p q h]
theorem nonnegative5110 (p : Pattern) : 0 ≤ d5110 p :=
  nonnegative_ite (p 138) (nonnegative5109 p) (nonnegative5083 p)
def d5111 (p : Pattern) : Int := if p 162 then d12 p else d5063 p
theorem agree5111 (p q : Pattern) (h : Agree support p q) : d5111 p = d5111 q := by
  simp only [d5111, h 162 (by decide), agree12 p q h, agree5063 p q h]
theorem nonnegative5111 (p : Pattern) : 0 ≤ d5111 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5063 p)
def d5112 (p : Pattern) : Int := if p 161 then d12 p else d5111 p
theorem agree5112 (p q : Pattern) (h : Agree support p q) : d5112 p = d5112 q := by
  simp only [d5112, h 161 (by decide), agree12 p q h, agree5111 p q h]
theorem nonnegative5112 (p : Pattern) : 0 ≤ d5112 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5111 p)
def d5113 (p : Pattern) : Int := if p 160 then d12 p else d5112 p
theorem agree5113 (p q : Pattern) (h : Agree support p q) : d5113 p = d5113 q := by
  simp only [d5113, h 160 (by decide), agree12 p q h, agree5112 p q h]
theorem nonnegative5113 (p : Pattern) : 0 ≤ d5113 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5112 p)
def d5114 (p : Pattern) : Int := if p 141 then d12 p else d5113 p
theorem agree5114 (p q : Pattern) (h : Agree support p q) : d5114 p = d5114 q := by
  simp only [d5114, h 141 (by decide), agree12 p q h, agree5113 p q h]
theorem nonnegative5114 (p : Pattern) : 0 ≤ d5114 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative5113 p)
def d5115 (p : Pattern) : Int := if p 138 then d5114 p else d5109 p
theorem agree5115 (p q : Pattern) (h : Agree support p q) : d5115 p = d5115 q := by
  simp only [d5115, h 138 (by decide), agree5114 p q h, agree5109 p q h]
theorem nonnegative5115 (p : Pattern) : 0 ≤ d5115 p :=
  nonnegative_ite (p 138) (nonnegative5114 p) (nonnegative5109 p)
def d5116 (p : Pattern) : Int := if p 116 then d5115 p else d5110 p
theorem agree5116 (p q : Pattern) (h : Agree support p q) : d5116 p = d5116 q := by
  simp only [d5116, h 116 (by decide), agree5115 p q h, agree5110 p q h]
theorem nonnegative5116 (p : Pattern) : 0 ≤ d5116 p :=
  nonnegative_ite (p 116) (nonnegative5115 p) (nonnegative5110 p)
def d5117 (p : Pattern) : Int := if p 138 then d12 p else d5109 p
theorem agree5117 (p q : Pattern) (h : Agree support p q) : d5117 p = d5117 q := by
  simp only [d5117, h 138 (by decide), agree12 p q h, agree5109 p q h]
theorem nonnegative5117 (p : Pattern) : 0 ≤ d5117 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5109 p)
def d5118 (p : Pattern) : Int := if p 116 then d5117 p else d5110 p
theorem agree5118 (p q : Pattern) (h : Agree support p q) : d5118 p = d5118 q := by
  simp only [d5118, h 116 (by decide), agree5117 p q h, agree5110 p q h]
theorem nonnegative5118 (p : Pattern) : 0 ≤ d5118 p :=
  nonnegative_ite (p 116) (nonnegative5117 p) (nonnegative5110 p)
def d5119 (p : Pattern) : Int := if p 115 then d5118 p else d5116 p
theorem agree5119 (p q : Pattern) (h : Agree support p q) : d5119 p = d5119 q := by
  simp only [d5119, h 115 (by decide), agree5118 p q h, agree5116 p q h]
theorem nonnegative5119 (p : Pattern) : 0 ≤ d5119 p :=
  nonnegative_ite (p 115) (nonnegative5118 p) (nonnegative5116 p)
def d5120 (p : Pattern) : Int := if p 71 then d5119 p else d5058 p
theorem agree5120 (p q : Pattern) (h : Agree support p q) : d5120 p = d5120 q := by
  simp only [d5120, h 71 (by decide), agree5119 p q h, agree5058 p q h]
theorem nonnegative5120 (p : Pattern) : 0 ≤ d5120 p :=
  nonnegative_ite (p 71) (nonnegative5119 p) (nonnegative5058 p)
def d5121 (p : Pattern) : Int := if p 49 then d5120 p else d5058 p
theorem agree5121 (p q : Pattern) (h : Agree support p q) : d5121 p = d5121 q := by
  simp only [d5121, h 49 (by decide), agree5120 p q h, agree5058 p q h]
theorem nonnegative5121 (p : Pattern) : 0 ≤ d5121 p :=
  nonnegative_ite (p 49) (nonnegative5120 p) (nonnegative5058 p)
def d5122 (p : Pattern) : Int := if p 182 then d2012 p else d18 p
theorem agree5122 (p q : Pattern) (h : Agree support p q) : d5122 p = d5122 q := by
  simp only [d5122, h 182 (by decide), agree2012 p q h, agree18 p q h]
theorem nonnegative5122 (p : Pattern) : 0 ≤ d5122 p :=
  nonnegative_ite (p 182) (nonnegative2012 p) (nonnegative18 p)
def d5123 (p : Pattern) : Int := if p 163 then d5122 p else d5017 p
theorem agree5123 (p q : Pattern) (h : Agree support p q) : d5123 p = d5123 q := by
  simp only [d5123, h 163 (by decide), agree5122 p q h, agree5017 p q h]
theorem nonnegative5123 (p : Pattern) : 0 ≤ d5123 p :=
  nonnegative_ite (p 163) (nonnegative5122 p) (nonnegative5017 p)
def d5124 (p : Pattern) : Int := if p 162 then d5123 p else d5017 p
theorem agree5124 (p q : Pattern) (h : Agree support p q) : d5124 p = d5124 q := by
  simp only [d5124, h 162 (by decide), agree5123 p q h, agree5017 p q h]
theorem nonnegative5124 (p : Pattern) : 0 ≤ d5124 p :=
  nonnegative_ite (p 162) (nonnegative5123 p) (nonnegative5017 p)
def d5125 (p : Pattern) : Int := if p 162 then d5025 p else d5123 p
theorem agree5125 (p q : Pattern) (h : Agree support p q) : d5125 p = d5125 q := by
  simp only [d5125, h 162 (by decide), agree5025 p q h, agree5123 p q h]
theorem nonnegative5125 (p : Pattern) : 0 ≤ d5125 p :=
  nonnegative_ite (p 162) (nonnegative5025 p) (nonnegative5123 p)
def d5126 (p : Pattern) : Int := if p 161 then d5125 p else d5124 p
theorem agree5126 (p q : Pattern) (h : Agree support p q) : d5126 p = d5126 q := by
  simp only [d5126, h 161 (by decide), agree5125 p q h, agree5124 p q h]
theorem nonnegative5126 (p : Pattern) : 0 ≤ d5126 p :=
  nonnegative_ite (p 161) (nonnegative5125 p) (nonnegative5124 p)
def d5127 (p : Pattern) : Int := if p 182 then d1724 p else d31 p
theorem agree5127 (p q : Pattern) (h : Agree support p q) : d5127 p = d5127 q := by
  simp only [d5127, h 182 (by decide), agree1724 p q h, agree31 p q h]
theorem nonnegative5127 (p : Pattern) : 0 ≤ d5127 p :=
  nonnegative_ite (p 182) (nonnegative1724 p) (nonnegative31 p)
def d5128 (p : Pattern) : Int := if p 163 then d5127 p else d5028 p
theorem agree5128 (p q : Pattern) (h : Agree support p q) : d5128 p = d5128 q := by
  simp only [d5128, h 163 (by decide), agree5127 p q h, agree5028 p q h]
theorem nonnegative5128 (p : Pattern) : 0 ≤ d5128 p :=
  nonnegative_ite (p 163) (nonnegative5127 p) (nonnegative5028 p)
def d5129 (p : Pattern) : Int := if p 182 then d1729 p else d31 p
theorem agree5129 (p q : Pattern) (h : Agree support p q) : d5129 p = d5129 q := by
  simp only [d5129, h 182 (by decide), agree1729 p q h, agree31 p q h]
theorem nonnegative5129 (p : Pattern) : 0 ≤ d5129 p :=
  nonnegative_ite (p 182) (nonnegative1729 p) (nonnegative31 p)
def d5130 (p : Pattern) : Int := if p 163 then d173 p else d5129 p
theorem agree5130 (p q : Pattern) (h : Agree support p q) : d5130 p = d5130 q := by
  simp only [d5130, h 163 (by decide), agree173 p q h, agree5129 p q h]
theorem nonnegative5130 (p : Pattern) : 0 ≤ d5130 p :=
  nonnegative_ite (p 163) (nonnegative173 p) (nonnegative5129 p)
def d5131 (p : Pattern) : Int := if p 162 then d5130 p else d5128 p
theorem agree5131 (p q : Pattern) (h : Agree support p q) : d5131 p = d5131 q := by
  simp only [d5131, h 162 (by decide), agree5130 p q h, agree5128 p q h]
theorem nonnegative5131 (p : Pattern) : 0 ≤ d5131 p :=
  nonnegative_ite (p 162) (nonnegative5130 p) (nonnegative5128 p)
def d5132 (p : Pattern) : Int := if p 161 then d177 p else d5131 p
theorem agree5132 (p q : Pattern) (h : Agree support p q) : d5132 p = d5132 q := by
  simp only [d5132, h 161 (by decide), agree177 p q h, agree5131 p q h]
theorem nonnegative5132 (p : Pattern) : 0 ≤ d5132 p :=
  nonnegative_ite (p 161) (nonnegative177 p) (nonnegative5131 p)
def d5133 (p : Pattern) : Int := if p 160 then d5132 p else d5126 p
theorem agree5133 (p q : Pattern) (h : Agree support p q) : d5133 p = d5133 q := by
  simp only [d5133, h 160 (by decide), agree5132 p q h, agree5126 p q h]
theorem nonnegative5133 (p : Pattern) : 0 ≤ d5133 p :=
  nonnegative_ite (p 160) (nonnegative5132 p) (nonnegative5126 p)
def d5134 (p : Pattern) : Int := if p 182 then d2030 p else d31 p
theorem agree5134 (p q : Pattern) (h : Agree support p q) : d5134 p = d5134 q := by
  simp only [d5134, h 182 (by decide), agree2030 p q h, agree31 p q h]
theorem nonnegative5134 (p : Pattern) : 0 ≤ d5134 p :=
  nonnegative_ite (p 182) (nonnegative2030 p) (nonnegative31 p)
def d5135 (p : Pattern) : Int := if p 163 then d5134 p else d5017 p
theorem agree5135 (p q : Pattern) (h : Agree support p q) : d5135 p = d5135 q := by
  simp only [d5135, h 163 (by decide), agree5134 p q h, agree5017 p q h]
theorem nonnegative5135 (p : Pattern) : 0 ≤ d5135 p :=
  nonnegative_ite (p 163) (nonnegative5134 p) (nonnegative5017 p)
def d5136 (p : Pattern) : Int := if p 163 then d5024 p else d5122 p
theorem agree5136 (p q : Pattern) (h : Agree support p q) : d5136 p = d5136 q := by
  simp only [d5136, h 163 (by decide), agree5024 p q h, agree5122 p q h]
theorem nonnegative5136 (p : Pattern) : 0 ≤ d5136 p :=
  nonnegative_ite (p 163) (nonnegative5024 p) (nonnegative5122 p)
def d5137 (p : Pattern) : Int := if p 162 then d5136 p else d5135 p
theorem agree5137 (p q : Pattern) (h : Agree support p q) : d5137 p = d5137 q := by
  simp only [d5137, h 162 (by decide), agree5136 p q h, agree5135 p q h]
theorem nonnegative5137 (p : Pattern) : 0 ≤ d5137 p :=
  nonnegative_ite (p 162) (nonnegative5136 p) (nonnegative5135 p)
def d5138 (p : Pattern) : Int := if p 163 then d5006 p else d5122 p
theorem agree5138 (p q : Pattern) (h : Agree support p q) : d5138 p = d5138 q := by
  simp only [d5138, h 163 (by decide), agree5006 p q h, agree5122 p q h]
theorem nonnegative5138 (p : Pattern) : 0 ≤ d5138 p :=
  nonnegative_ite (p 163) (nonnegative5006 p) (nonnegative5122 p)
def d5139 (p : Pattern) : Int := if p 162 then d5009 p else d5138 p
theorem agree5139 (p q : Pattern) (h : Agree support p q) : d5139 p = d5139 q := by
  simp only [d5139, h 162 (by decide), agree5009 p q h, agree5138 p q h]
theorem nonnegative5139 (p : Pattern) : 0 ≤ d5139 p :=
  nonnegative_ite (p 162) (nonnegative5009 p) (nonnegative5138 p)
def d5140 (p : Pattern) : Int := if p 161 then d5139 p else d5137 p
theorem agree5140 (p q : Pattern) (h : Agree support p q) : d5140 p = d5140 q := by
  simp only [d5140, h 161 (by decide), agree5139 p q h, agree5137 p q h]
theorem nonnegative5140 (p : Pattern) : 0 ≤ d5140 p :=
  nonnegative_ite (p 161) (nonnegative5139 p) (nonnegative5137 p)
def d5141 (p : Pattern) : Int := if p 163 then d43 p else d5127 p
theorem agree5141 (p q : Pattern) (h : Agree support p q) : d5141 p = d5141 q := by
  simp only [d5141, h 163 (by decide), agree43 p q h, agree5127 p q h]
theorem nonnegative5141 (p : Pattern) : 0 ≤ d5141 p :=
  nonnegative_ite (p 163) (nonnegative43 p) (nonnegative5127 p)
def d5142 (p : Pattern) : Int := if p 162 then d181 p else d5141 p
theorem agree5142 (p q : Pattern) (h : Agree support p q) : d5142 p = d5142 q := by
  simp only [d5142, h 162 (by decide), agree181 p q h, agree5141 p q h]
theorem nonnegative5142 (p : Pattern) : 0 ≤ d5142 p :=
  nonnegative_ite (p 162) (nonnegative181 p) (nonnegative5141 p)
def d5143 (p : Pattern) : Int := if p 161 then d184 p else d5142 p
theorem agree5143 (p q : Pattern) (h : Agree support p q) : d5143 p = d5143 q := by
  simp only [d5143, h 161 (by decide), agree184 p q h, agree5142 p q h]
theorem nonnegative5143 (p : Pattern) : 0 ≤ d5143 p :=
  nonnegative_ite (p 161) (nonnegative184 p) (nonnegative5142 p)
def d5144 (p : Pattern) : Int := if p 160 then d5143 p else d5140 p
theorem agree5144 (p q : Pattern) (h : Agree support p q) : d5144 p = d5144 q := by
  simp only [d5144, h 160 (by decide), agree5143 p q h, agree5140 p q h]
theorem nonnegative5144 (p : Pattern) : 0 ≤ d5144 p :=
  nonnegative_ite (p 160) (nonnegative5143 p) (nonnegative5140 p)
def d5145 (p : Pattern) : Int := if p 141 then d5144 p else d5133 p
theorem agree5145 (p q : Pattern) (h : Agree support p q) : d5145 p = d5145 q := by
  simp only [d5145, h 141 (by decide), agree5144 p q h, agree5133 p q h]
theorem nonnegative5145 (p : Pattern) : 0 ≤ d5145 p :=
  nonnegative_ite (p 141) (nonnegative5144 p) (nonnegative5133 p)
def d5146 (p : Pattern) : Int := if p 182 then d2048 p else d14 p
theorem agree5146 (p q : Pattern) (h : Agree support p q) : d5146 p = d5146 q := by
  simp only [d5146, h 182 (by decide), agree2048 p q h, agree14 p q h]
theorem nonnegative5146 (p : Pattern) : 0 ≤ d5146 p :=
  nonnegative_ite (p 182) (nonnegative2048 p) (nonnegative14 p)
def d5147 (p : Pattern) : Int := if p 182 then d2054 p else d14 p
theorem agree5147 (p q : Pattern) (h : Agree support p q) : d5147 p = d5147 q := by
  simp only [d5147, h 182 (by decide), agree2054 p q h, agree14 p q h]
theorem nonnegative5147 (p : Pattern) : 0 ≤ d5147 p :=
  nonnegative_ite (p 182) (nonnegative2054 p) (nonnegative14 p)
def d5148 (p : Pattern) : Int := if p 163 then d5147 p else d5146 p
theorem agree5148 (p q : Pattern) (h : Agree support p q) : d5148 p = d5148 q := by
  simp only [d5148, h 163 (by decide), agree5147 p q h, agree5146 p q h]
theorem nonnegative5148 (p : Pattern) : 0 ≤ d5148 p :=
  nonnegative_ite (p 163) (nonnegative5147 p) (nonnegative5146 p)
def d5149 (p : Pattern) : Int := if p 162 then d5030 p else d5148 p
theorem agree5149 (p q : Pattern) (h : Agree support p q) : d5149 p = d5149 q := by
  simp only [d5149, h 162 (by decide), agree5030 p q h, agree5148 p q h]
theorem nonnegative5149 (p : Pattern) : 0 ≤ d5149 p :=
  nonnegative_ite (p 162) (nonnegative5030 p) (nonnegative5148 p)
def d5150 (p : Pattern) : Int := if p 161 then d5031 p else d5149 p
theorem agree5150 (p q : Pattern) (h : Agree support p q) : d5150 p = d5150 q := by
  simp only [d5150, h 161 (by decide), agree5031 p q h, agree5149 p q h]
theorem nonnegative5150 (p : Pattern) : 0 ≤ d5150 p :=
  nonnegative_ite (p 161) (nonnegative5031 p) (nonnegative5149 p)
def d5151 (p : Pattern) : Int := if p 182 then d2061 p else d191 p
theorem agree5151 (p q : Pattern) (h : Agree support p q) : d5151 p = d5151 q := by
  simp only [d5151, h 182 (by decide), agree2061 p q h, agree191 p q h]
theorem nonnegative5151 (p : Pattern) : 0 ≤ d5151 p :=
  nonnegative_ite (p 182) (nonnegative2061 p) (nonnegative191 p)
def d5152 (p : Pattern) : Int := if p 163 then d5151 p else d5021 p
theorem agree5152 (p q : Pattern) (h : Agree support p q) : d5152 p = d5152 q := by
  simp only [d5152, h 163 (by decide), agree5151 p q h, agree5021 p q h]
theorem nonnegative5152 (p : Pattern) : 0 ≤ d5152 p :=
  nonnegative_ite (p 163) (nonnegative5151 p) (nonnegative5021 p)
def d5153 (p : Pattern) : Int := if p 162 then d12 p else d5152 p
theorem agree5153 (p q : Pattern) (h : Agree support p q) : d5153 p = d5153 q := by
  simp only [d5153, h 162 (by decide), agree12 p q h, agree5152 p q h]
theorem nonnegative5153 (p : Pattern) : 0 ≤ d5153 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5152 p)
def d5154 (p : Pattern) : Int := if p 161 then d12 p else d5153 p
theorem agree5154 (p q : Pattern) (h : Agree support p q) : d5154 p = d5154 q := by
  simp only [d5154, h 161 (by decide), agree12 p q h, agree5153 p q h]
theorem nonnegative5154 (p : Pattern) : 0 ≤ d5154 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5153 p)
def d5155 (p : Pattern) : Int := if p 160 then d5154 p else d5150 p
theorem agree5155 (p q : Pattern) (h : Agree support p q) : d5155 p = d5155 q := by
  simp only [d5155, h 160 (by decide), agree5154 p q h, agree5150 p q h]
theorem nonnegative5155 (p : Pattern) : 0 ≤ d5155 p :=
  nonnegative_ite (p 160) (nonnegative5154 p) (nonnegative5150 p)
def d5156 (p : Pattern) : Int := if p 182 then d2071 p else d31 p
theorem agree5156 (p q : Pattern) (h : Agree support p q) : d5156 p = d5156 q := by
  simp only [d5156, h 182 (by decide), agree2071 p q h, agree31 p q h]
theorem nonnegative5156 (p : Pattern) : 0 ≤ d5156 p :=
  nonnegative_ite (p 182) (nonnegative2071 p) (nonnegative31 p)
def d5157 (p : Pattern) : Int := if p 163 then d5028 p else d5156 p
theorem agree5157 (p q : Pattern) (h : Agree support p q) : d5157 p = d5157 q := by
  simp only [d5157, h 163 (by decide), agree5028 p q h, agree5156 p q h]
theorem nonnegative5157 (p : Pattern) : 0 ≤ d5157 p :=
  nonnegative_ite (p 163) (nonnegative5028 p) (nonnegative5156 p)
def d5158 (p : Pattern) : Int := if p 163 then d5008 p else d5021 p
theorem agree5158 (p q : Pattern) (h : Agree support p q) : d5158 p = d5158 q := by
  simp only [d5158, h 163 (by decide), agree5008 p q h, agree5021 p q h]
theorem nonnegative5158 (p : Pattern) : 0 ≤ d5158 p :=
  nonnegative_ite (p 163) (nonnegative5008 p) (nonnegative5021 p)
def d5159 (p : Pattern) : Int := if p 162 then d5158 p else d5157 p
theorem agree5159 (p q : Pattern) (h : Agree support p q) : d5159 p = d5159 q := by
  simp only [d5159, h 162 (by decide), agree5158 p q h, agree5157 p q h]
theorem nonnegative5159 (p : Pattern) : 0 ≤ d5159 p :=
  nonnegative_ite (p 162) (nonnegative5158 p) (nonnegative5157 p)
end NetHack.Sokoban22Refined85
