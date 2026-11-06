/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d120 (p : Pattern) : Int := if p 246 then d119 p else d7 p
theorem agree120 (p q : Pattern) (h : Agree support p q) : d120 p = d120 q := by
  simp only [d120, h 246 (by decide), agree119 p q h, agree7 p q h]
theorem nonnegative120 (p : Pattern) : 0 ≤ d120 p :=
  nonnegative_ite (p 246) (nonnegative119 p) (nonnegative7 p)
def d121 (p : Pattern) : Int := if p 204 then d12 p else d120 p
theorem agree121 (p q : Pattern) (h : Agree support p q) : d121 p = d121 q := by
  simp only [d121, h 204 (by decide), agree12 p q h, agree120 p q h]
theorem nonnegative121 (p : Pattern) : 0 ≤ d121 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative120 p)
def d122 (p : Pattern) : Int := if p 182 then d121 p else d103 p
theorem agree122 (p q : Pattern) (h : Agree support p q) : d122 p = d122 q := by
  simp only [d122, h 182 (by decide), agree121 p q h, agree103 p q h]
theorem nonnegative122 (p : Pattern) : 0 ≤ d122 p :=
  nonnegative_ite (p 182) (nonnegative121 p) (nonnegative103 p)
def d123 (p : Pattern) : Int := if p 163 then d122 p else d118 p
theorem agree123 (p q : Pattern) (h : Agree support p q) : d123 p = d123 q := by
  simp only [d123, h 163 (by decide), agree122 p q h, agree118 p q h]
theorem nonnegative123 (p : Pattern) : 0 ≤ d123 p :=
  nonnegative_ite (p 163) (nonnegative122 p) (nonnegative118 p)
def d124 (p : Pattern) : Int := if p 182 then d12 p else d103 p
theorem agree124 (p q : Pattern) (h : Agree support p q) : d124 p = d124 q := by
  simp only [d124, h 182 (by decide), agree12 p q h, agree103 p q h]
theorem nonnegative124 (p : Pattern) : 0 ≤ d124 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative103 p)
def d125 (p : Pattern) : Int := if p 182 then d12 p else d107 p
theorem agree125 (p q : Pattern) (h : Agree support p q) : d125 p = d125 q := by
  simp only [d125, h 182 (by decide), agree12 p q h, agree107 p q h]
theorem nonnegative125 (p : Pattern) : 0 ≤ d125 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative107 p)
def d126 (p : Pattern) : Int := if p 163 then d125 p else d124 p
theorem agree126 (p q : Pattern) (h : Agree support p q) : d126 p = d126 q := by
  simp only [d126, h 163 (by decide), agree125 p q h, agree124 p q h]
theorem nonnegative126 (p : Pattern) : 0 ≤ d126 p :=
  nonnegative_ite (p 163) (nonnegative125 p) (nonnegative124 p)
def d127 (p : Pattern) : Int := if p 162 then d126 p else d123 p
theorem agree127 (p q : Pattern) (h : Agree support p q) : d127 p = d127 q := by
  simp only [d127, h 162 (by decide), agree126 p q h, agree123 p q h]
theorem nonnegative127 (p : Pattern) : 0 ≤ d127 p :=
  nonnegative_ite (p 162) (nonnegative126 p) (nonnegative123 p)
def d128 (p : Pattern) : Int := if p 163 then d12 p else d70 p
theorem agree128 (p q : Pattern) (h : Agree support p q) : d128 p = d128 q := by
  simp only [d128, h 163 (by decide), agree12 p q h, agree70 p q h]
theorem nonnegative128 (p : Pattern) : 0 ≤ d128 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative70 p)
def d129 (p : Pattern) : Int := if p 162 then d128 p else d126 p
theorem agree129 (p q : Pattern) (h : Agree support p q) : d129 p = d129 q := by
  simp only [d129, h 162 (by decide), agree128 p q h, agree126 p q h]
theorem nonnegative129 (p : Pattern) : 0 ≤ d129 p :=
  nonnegative_ite (p 162) (nonnegative128 p) (nonnegative126 p)
def d130 (p : Pattern) : Int := if p 161 then d129 p else d127 p
theorem agree130 (p q : Pattern) (h : Agree support p q) : d130 p = d130 q := by
  simp only [d130, h 161 (by decide), agree129 p q h, agree127 p q h]
theorem nonnegative130 (p : Pattern) : 0 ≤ d130 p :=
  nonnegative_ite (p 161) (nonnegative129 p) (nonnegative127 p)
def d131 (p : Pattern) : Int := if p 160 then d130 p else d114 p
theorem agree131 (p q : Pattern) (h : Agree support p q) : d131 p = d131 q := by
  simp only [d131, h 160 (by decide), agree130 p q h, agree114 p q h]
theorem nonnegative131 (p : Pattern) : 0 ≤ d131 p :=
  nonnegative_ite (p 160) (nonnegative130 p) (nonnegative114 p)
def d132 (p : Pattern) : Int := if p 182 then d117 p else d116 p
theorem agree132 (p q : Pattern) (h : Agree support p q) : d132 p = d132 q := by
  simp only [d132, h 182 (by decide), agree117 p q h, agree116 p q h]
theorem nonnegative132 (p : Pattern) : 0 ≤ d132 p :=
  nonnegative_ite (p 182) (nonnegative117 p) (nonnegative116 p)
def d133 (p : Pattern) : Int := if p 163 then d132 p else d105 p
theorem agree133 (p q : Pattern) (h : Agree support p q) : d133 p = d133 q := by
  simp only [d133, h 163 (by decide), agree132 p q h, agree105 p q h]
theorem nonnegative133 (p : Pattern) : 0 ≤ d133 p :=
  nonnegative_ite (p 163) (nonnegative132 p) (nonnegative105 p)
def d134 (p : Pattern) : Int := if p 163 then d60 p else d109 p
theorem agree134 (p q : Pattern) (h : Agree support p q) : d134 p = d134 q := by
  simp only [d134, h 163 (by decide), agree60 p q h, agree109 p q h]
theorem nonnegative134 (p : Pattern) : 0 ≤ d134 p :=
  nonnegative_ite (p 163) (nonnegative60 p) (nonnegative109 p)
def d135 (p : Pattern) : Int := if p 162 then d134 p else d133 p
theorem agree135 (p q : Pattern) (h : Agree support p q) : d135 p = d135 q := by
  simp only [d135, h 162 (by decide), agree134 p q h, agree133 p q h]
theorem nonnegative135 (p : Pattern) : 0 ≤ d135 p :=
  nonnegative_ite (p 162) (nonnegative134 p) (nonnegative133 p)
def d136 (p : Pattern) : Int := if p 163 then d62 p else d109 p
theorem agree136 (p q : Pattern) (h : Agree support p q) : d136 p = d136 q := by
  simp only [d136, h 163 (by decide), agree62 p q h, agree109 p q h]
theorem nonnegative136 (p : Pattern) : 0 ≤ d136 p :=
  nonnegative_ite (p 163) (nonnegative62 p) (nonnegative109 p)
def d137 (p : Pattern) : Int := if p 162 then d12 p else d136 p
theorem agree137 (p q : Pattern) (h : Agree support p q) : d137 p = d137 q := by
  simp only [d137, h 162 (by decide), agree12 p q h, agree136 p q h]
theorem nonnegative137 (p : Pattern) : 0 ≤ d137 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative136 p)
def d138 (p : Pattern) : Int := if p 161 then d137 p else d135 p
theorem agree138 (p q : Pattern) (h : Agree support p q) : d138 p = d138 q := by
  simp only [d138, h 161 (by decide), agree137 p q h, agree135 p q h]
theorem nonnegative138 (p : Pattern) : 0 ≤ d138 p :=
  nonnegative_ite (p 161) (nonnegative137 p) (nonnegative135 p)
def d139 (p : Pattern) : Int := if p 182 then d12 p else d116 p
theorem agree139 (p q : Pattern) (h : Agree support p q) : d139 p = d139 q := by
  simp only [d139, h 182 (by decide), agree12 p q h, agree116 p q h]
theorem nonnegative139 (p : Pattern) : 0 ≤ d139 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative116 p)
def d140 (p : Pattern) : Int := if p 163 then d139 p else d122 p
theorem agree140 (p q : Pattern) (h : Agree support p q) : d140 p = d140 q := by
  simp only [d140, h 163 (by decide), agree139 p q h, agree122 p q h]
theorem nonnegative140 (p : Pattern) : 0 ≤ d140 p :=
  nonnegative_ite (p 163) (nonnegative139 p) (nonnegative122 p)
def d141 (p : Pattern) : Int := if p 163 then d70 p else d125 p
theorem agree141 (p q : Pattern) (h : Agree support p q) : d141 p = d141 q := by
  simp only [d141, h 163 (by decide), agree70 p q h, agree125 p q h]
theorem nonnegative141 (p : Pattern) : 0 ≤ d141 p :=
  nonnegative_ite (p 163) (nonnegative70 p) (nonnegative125 p)
def d142 (p : Pattern) : Int := if p 162 then d141 p else d140 p
theorem agree142 (p q : Pattern) (h : Agree support p q) : d142 p = d142 q := by
  simp only [d142, h 162 (by decide), agree141 p q h, agree140 p q h]
theorem nonnegative142 (p : Pattern) : 0 ≤ d142 p :=
  nonnegative_ite (p 162) (nonnegative141 p) (nonnegative140 p)
def d143 (p : Pattern) : Int := if p 163 then d72 p else d125 p
theorem agree143 (p q : Pattern) (h : Agree support p q) : d143 p = d143 q := by
  simp only [d143, h 163 (by decide), agree72 p q h, agree125 p q h]
theorem nonnegative143 (p : Pattern) : 0 ≤ d143 p :=
  nonnegative_ite (p 163) (nonnegative72 p) (nonnegative125 p)
def d144 (p : Pattern) : Int := if p 162 then d12 p else d143 p
theorem agree144 (p q : Pattern) (h : Agree support p q) : d144 p = d144 q := by
  simp only [d144, h 162 (by decide), agree12 p q h, agree143 p q h]
theorem nonnegative144 (p : Pattern) : 0 ≤ d144 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative143 p)
def d145 (p : Pattern) : Int := if p 161 then d144 p else d142 p
theorem agree145 (p q : Pattern) (h : Agree support p q) : d145 p = d145 q := by
  simp only [d145, h 161 (by decide), agree144 p q h, agree142 p q h]
theorem nonnegative145 (p : Pattern) : 0 ≤ d145 p :=
  nonnegative_ite (p 161) (nonnegative144 p) (nonnegative142 p)
def d146 (p : Pattern) : Int := if p 160 then d145 p else d138 p
theorem agree146 (p q : Pattern) (h : Agree support p q) : d146 p = d146 q := by
  simp only [d146, h 160 (by decide), agree145 p q h, agree138 p q h]
theorem nonnegative146 (p : Pattern) : 0 ≤ d146 p :=
  nonnegative_ite (p 160) (nonnegative145 p) (nonnegative138 p)
def d147 (p : Pattern) : Int := if p 141 then d146 p else d131 p
theorem agree147 (p q : Pattern) (h : Agree support p q) : d147 p = d147 q := by
  simp only [d147, h 141 (by decide), agree146 p q h, agree131 p q h]
theorem nonnegative147 (p : Pattern) : 0 ≤ d147 p :=
  nonnegative_ite (p 141) (nonnegative146 p) (nonnegative131 p)
def d148 (p : Pattern) : Int := if p 182 then d121 p else d120 p
theorem agree148 (p q : Pattern) (h : Agree support p q) : d148 p = d148 q := by
  simp only [d148, h 182 (by decide), agree121 p q h, agree120 p q h]
theorem nonnegative148 (p : Pattern) : 0 ≤ d148 p :=
  nonnegative_ite (p 182) (nonnegative121 p) (nonnegative120 p)
def d149 (p : Pattern) : Int := if p 163 then d148 p else d132 p
theorem agree149 (p q : Pattern) (h : Agree support p q) : d149 p = d149 q := by
  simp only [d149, h 163 (by decide), agree148 p q h, agree132 p q h]
theorem nonnegative149 (p : Pattern) : 0 ≤ d149 p :=
  nonnegative_ite (p 163) (nonnegative148 p) (nonnegative132 p)
def d150 (p : Pattern) : Int := if p 162 then d12 p else d149 p
theorem agree150 (p q : Pattern) (h : Agree support p q) : d150 p = d150 q := by
  simp only [d150, h 162 (by decide), agree12 p q h, agree149 p q h]
theorem nonnegative150 (p : Pattern) : 0 ≤ d150 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative149 p)
def d151 (p : Pattern) : Int := if p 161 then d12 p else d150 p
theorem agree151 (p q : Pattern) (h : Agree support p q) : d151 p = d151 q := by
  simp only [d151, h 161 (by decide), agree12 p q h, agree150 p q h]
theorem nonnegative151 (p : Pattern) : 0 ≤ d151 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative150 p)
def d152 (p : Pattern) : Int := if p 160 then d151 p else d114 p
theorem agree152 (p q : Pattern) (h : Agree support p q) : d152 p = d152 q := by
  simp only [d152, h 160 (by decide), agree151 p q h, agree114 p q h]
theorem nonnegative152 (p : Pattern) : 0 ≤ d152 p :=
  nonnegative_ite (p 160) (nonnegative151 p) (nonnegative114 p)
def d153 (p : Pattern) : Int := if p 163 then d12 p else d148 p
theorem agree153 (p q : Pattern) (h : Agree support p q) : d153 p = d153 q := by
  simp only [d153, h 163 (by decide), agree12 p q h, agree148 p q h]
theorem nonnegative153 (p : Pattern) : 0 ≤ d153 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative148 p)
def d154 (p : Pattern) : Int := if p 162 then d12 p else d153 p
theorem agree154 (p q : Pattern) (h : Agree support p q) : d154 p = d154 q := by
  simp only [d154, h 162 (by decide), agree12 p q h, agree153 p q h]
theorem nonnegative154 (p : Pattern) : 0 ≤ d154 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative153 p)
def d155 (p : Pattern) : Int := if p 161 then d12 p else d154 p
theorem agree155 (p q : Pattern) (h : Agree support p q) : d155 p = d155 q := by
  simp only [d155, h 161 (by decide), agree12 p q h, agree154 p q h]
theorem nonnegative155 (p : Pattern) : 0 ≤ d155 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative154 p)
def d156 (p : Pattern) : Int := if p 160 then d155 p else d138 p
theorem agree156 (p q : Pattern) (h : Agree support p q) : d156 p = d156 q := by
  simp only [d156, h 160 (by decide), agree155 p q h, agree138 p q h]
theorem nonnegative156 (p : Pattern) : 0 ≤ d156 p :=
  nonnegative_ite (p 160) (nonnegative155 p) (nonnegative138 p)
def d157 (p : Pattern) : Int := if p 141 then d156 p else d152 p
theorem agree157 (p q : Pattern) (h : Agree support p q) : d157 p = d157 q := by
  simp only [d157, h 141 (by decide), agree156 p q h, agree152 p q h]
theorem nonnegative157 (p : Pattern) : 0 ≤ d157 p :=
  nonnegative_ite (p 141) (nonnegative156 p) (nonnegative152 p)
def d158 (p : Pattern) : Int := if p 138 then d157 p else d147 p
theorem agree158 (p q : Pattern) (h : Agree support p q) : d158 p = d158 q := by
  simp only [d158, h 138 (by decide), agree157 p q h, agree147 p q h]
theorem nonnegative158 (p : Pattern) : 0 ≤ d158 p :=
  nonnegative_ite (p 138) (nonnegative157 p) (nonnegative147 p)
def d159 (p : Pattern) : Int := if p 162 then d12 p else d112 p
theorem agree159 (p q : Pattern) (h : Agree support p q) : d159 p = d159 q := by
  simp only [d159, h 162 (by decide), agree12 p q h, agree112 p q h]
theorem nonnegative159 (p : Pattern) : 0 ≤ d159 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative112 p)
def d160 (p : Pattern) : Int := if p 161 then d12 p else d159 p
theorem agree160 (p q : Pattern) (h : Agree support p q) : d160 p = d160 q := by
  simp only [d160, h 161 (by decide), agree12 p q h, agree159 p q h]
theorem nonnegative160 (p : Pattern) : 0 ≤ d160 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative159 p)
def d161 (p : Pattern) : Int := if p 160 then d12 p else d160 p
theorem agree161 (p q : Pattern) (h : Agree support p q) : d161 p = d161 q := by
  simp only [d161, h 160 (by decide), agree12 p q h, agree160 p q h]
theorem nonnegative161 (p : Pattern) : 0 ≤ d161 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative160 p)
def d162 (p : Pattern) : Int := if p 141 then d12 p else d161 p
theorem agree162 (p q : Pattern) (h : Agree support p q) : d162 p = d162 q := by
  simp only [d162, h 141 (by decide), agree12 p q h, agree161 p q h]
theorem nonnegative162 (p : Pattern) : 0 ≤ d162 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative161 p)
def d163 (p : Pattern) : Int := if p 138 then d162 p else d157 p
theorem agree163 (p q : Pattern) (h : Agree support p q) : d163 p = d163 q := by
  simp only [d163, h 138 (by decide), agree162 p q h, agree157 p q h]
theorem nonnegative163 (p : Pattern) : 0 ≤ d163 p :=
  nonnegative_ite (p 138) (nonnegative162 p) (nonnegative157 p)
def d164 (p : Pattern) : Int := if p 116 then d163 p else d158 p
theorem agree164 (p q : Pattern) (h : Agree support p q) : d164 p = d164 q := by
  simp only [d164, h 116 (by decide), agree163 p q h, agree158 p q h]
theorem nonnegative164 (p : Pattern) : 0 ≤ d164 p :=
  nonnegative_ite (p 116) (nonnegative163 p) (nonnegative158 p)
def d165 (p : Pattern) : Int := if p 138 then d12 p else d157 p
theorem agree165 (p q : Pattern) (h : Agree support p q) : d165 p = d165 q := by
  simp only [d165, h 138 (by decide), agree12 p q h, agree157 p q h]
theorem nonnegative165 (p : Pattern) : 0 ≤ d165 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative157 p)
def d166 (p : Pattern) : Int := if p 116 then d165 p else d158 p
theorem agree166 (p q : Pattern) (h : Agree support p q) : d166 p = d166 q := by
  simp only [d166, h 116 (by decide), agree165 p q h, agree158 p q h]
theorem nonnegative166 (p : Pattern) : 0 ≤ d166 p :=
  nonnegative_ite (p 116) (nonnegative165 p) (nonnegative158 p)
def d167 (p : Pattern) : Int := if p 115 then d166 p else d164 p
theorem agree167 (p q : Pattern) (h : Agree support p q) : d167 p = d167 q := by
  simp only [d167, h 115 (by decide), agree166 p q h, agree164 p q h]
theorem nonnegative167 (p : Pattern) : 0 ≤ d167 p :=
  nonnegative_ite (p 115) (nonnegative166 p) (nonnegative164 p)
def d168 (p : Pattern) : Int := if p 71 then d167 p else d101 p
theorem agree168 (p q : Pattern) (h : Agree support p q) : d168 p = d168 q := by
  simp only [d168, h 71 (by decide), agree167 p q h, agree101 p q h]
theorem nonnegative168 (p : Pattern) : 0 ≤ d168 p :=
  nonnegative_ite (p 71) (nonnegative167 p) (nonnegative101 p)
def d169 (p : Pattern) : Int := if p 49 then d168 p else d101 p
theorem agree169 (p q : Pattern) (h : Agree support p q) : d169 p = d169 q := by
  simp only [d169, h 49 (by decide), agree168 p q h, agree101 p q h]
theorem nonnegative169 (p : Pattern) : 0 ≤ d169 p :=
  nonnegative_ite (p 49) (nonnegative168 p) (nonnegative101 p)
def d170 (p : Pattern) : Int := if p 182 then d36 p else d31 p
theorem agree170 (p q : Pattern) (h : Agree support p q) : d170 p = d170 q := by
  simp only [d170, h 182 (by decide), agree36 p q h, agree31 p q h]
theorem nonnegative170 (p : Pattern) : 0 ≤ d170 p :=
  nonnegative_ite (p 182) (nonnegative36 p) (nonnegative31 p)
def d171 (p : Pattern) : Int := if p 163 then d170 p else d53 p
theorem agree171 (p q : Pattern) (h : Agree support p q) : d171 p = d171 q := by
  simp only [d171, h 163 (by decide), agree170 p q h, agree53 p q h]
theorem nonnegative171 (p : Pattern) : 0 ≤ d171 p :=
  nonnegative_ite (p 163) (nonnegative170 p) (nonnegative53 p)
def d172 (p : Pattern) : Int := if p 182 then d41 p else d31 p
theorem agree172 (p q : Pattern) (h : Agree support p q) : d172 p = d172 q := by
  simp only [d172, h 182 (by decide), agree41 p q h, agree31 p q h]
theorem nonnegative172 (p : Pattern) : 0 ≤ d172 p :=
  nonnegative_ite (p 182) (nonnegative41 p) (nonnegative31 p)
def d173 (p : Pattern) : Int := if p 182 then d12 p else d35 p
theorem agree173 (p q : Pattern) (h : Agree support p q) : d173 p = d173 q := by
  simp only [d173, h 182 (by decide), agree12 p q h, agree35 p q h]
theorem nonnegative173 (p : Pattern) : 0 ≤ d173 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative35 p)
def d174 (p : Pattern) : Int := if p 163 then d173 p else d172 p
theorem agree174 (p q : Pattern) (h : Agree support p q) : d174 p = d174 q := by
  simp only [d174, h 163 (by decide), agree173 p q h, agree172 p q h]
theorem nonnegative174 (p : Pattern) : 0 ≤ d174 p :=
  nonnegative_ite (p 163) (nonnegative173 p) (nonnegative172 p)
def d175 (p : Pattern) : Int := if p 162 then d174 p else d171 p
theorem agree175 (p q : Pattern) (h : Agree support p q) : d175 p = d175 q := by
  simp only [d175, h 162 (by decide), agree174 p q h, agree171 p q h]
theorem nonnegative175 (p : Pattern) : 0 ≤ d175 p :=
  nonnegative_ite (p 162) (nonnegative174 p) (nonnegative171 p)
def d176 (p : Pattern) : Int := if p 163 then d173 p else d66 p
theorem agree176 (p q : Pattern) (h : Agree support p q) : d176 p = d176 q := by
  simp only [d176, h 163 (by decide), agree173 p q h, agree66 p q h]
theorem nonnegative176 (p : Pattern) : 0 ≤ d176 p :=
  nonnegative_ite (p 163) (nonnegative173 p) (nonnegative66 p)
def d177 (p : Pattern) : Int := if p 162 then d73 p else d176 p
theorem agree177 (p q : Pattern) (h : Agree support p q) : d177 p = d177 q := by
  simp only [d177, h 162 (by decide), agree73 p q h, agree176 p q h]
theorem nonnegative177 (p : Pattern) : 0 ≤ d177 p :=
  nonnegative_ite (p 162) (nonnegative73 p) (nonnegative176 p)
def d178 (p : Pattern) : Int := if p 161 then d177 p else d175 p
theorem agree178 (p q : Pattern) (h : Agree support p q) : d178 p = d178 q := by
  simp only [d178, h 161 (by decide), agree177 p q h, agree175 p q h]
theorem nonnegative178 (p : Pattern) : 0 ≤ d178 p :=
  nonnegative_ite (p 161) (nonnegative177 p) (nonnegative175 p)
def d179 (p : Pattern) : Int := if p 160 then d178 p else d29 p
theorem agree179 (p q : Pattern) (h : Agree support p q) : d179 p = d179 q := by
  simp only [d179, h 160 (by decide), agree178 p q h, agree29 p q h]
theorem nonnegative179 (p : Pattern) : 0 ≤ d179 p :=
  nonnegative_ite (p 160) (nonnegative178 p) (nonnegative29 p)
def d180 (p : Pattern) : Int := if p 163 then d43 p else d170 p
theorem agree180 (p q : Pattern) (h : Agree support p q) : d180 p = d180 q := by
  simp only [d180, h 163 (by decide), agree43 p q h, agree170 p q h]
theorem nonnegative180 (p : Pattern) : 0 ≤ d180 p :=
  nonnegative_ite (p 163) (nonnegative43 p) (nonnegative170 p)
def d181 (p : Pattern) : Int := if p 163 then d72 p else d173 p
theorem agree181 (p q : Pattern) (h : Agree support p q) : d181 p = d181 q := by
  simp only [d181, h 163 (by decide), agree72 p q h, agree173 p q h]
theorem nonnegative181 (p : Pattern) : 0 ≤ d181 p :=
  nonnegative_ite (p 163) (nonnegative72 p) (nonnegative173 p)
def d182 (p : Pattern) : Int := if p 162 then d181 p else d180 p
theorem agree182 (p q : Pattern) (h : Agree support p q) : d182 p = d182 q := by
  simp only [d182, h 162 (by decide), agree181 p q h, agree180 p q h]
theorem nonnegative182 (p : Pattern) : 0 ≤ d182 p :=
  nonnegative_ite (p 162) (nonnegative181 p) (nonnegative180 p)
def d183 (p : Pattern) : Int := if p 163 then d12 p else d173 p
theorem agree183 (p q : Pattern) (h : Agree support p q) : d183 p = d183 q := by
  simp only [d183, h 163 (by decide), agree12 p q h, agree173 p q h]
theorem nonnegative183 (p : Pattern) : 0 ≤ d183 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative173 p)
def d184 (p : Pattern) : Int := if p 162 then d12 p else d183 p
theorem agree184 (p q : Pattern) (h : Agree support p q) : d184 p = d184 q := by
  simp only [d184, h 162 (by decide), agree12 p q h, agree183 p q h]
theorem nonnegative184 (p : Pattern) : 0 ≤ d184 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative183 p)
def d185 (p : Pattern) : Int := if p 161 then d184 p else d182 p
theorem agree185 (p q : Pattern) (h : Agree support p q) : d185 p = d185 q := by
  simp only [d185, h 161 (by decide), agree184 p q h, agree182 p q h]
theorem nonnegative185 (p : Pattern) : 0 ≤ d185 p :=
  nonnegative_ite (p 161) (nonnegative184 p) (nonnegative182 p)
def d186 (p : Pattern) : Int := if p 160 then d185 p else d65 p
theorem agree186 (p q : Pattern) (h : Agree support p q) : d186 p = d186 q := by
  simp only [d186, h 160 (by decide), agree185 p q h, agree65 p q h]
theorem nonnegative186 (p : Pattern) : 0 ≤ d186 p :=
  nonnegative_ite (p 160) (nonnegative185 p) (nonnegative65 p)
def d187 (p : Pattern) : Int := if p 141 then d186 p else d179 p
theorem agree187 (p q : Pattern) (h : Agree support p q) : d187 p = d187 q := by
  simp only [d187, h 141 (by decide), agree186 p q h, agree179 p q h]
theorem nonnegative187 (p : Pattern) : 0 ≤ d187 p :=
  nonnegative_ite (p 141) (nonnegative186 p) (nonnegative179 p)
def d188 (p : Pattern) : Int := if p 162 then d79 p else d16 p
theorem agree188 (p q : Pattern) (h : Agree support p q) : d188 p = d188 q := by
  simp only [d188, h 162 (by decide), agree79 p q h, agree16 p q h]
theorem nonnegative188 (p : Pattern) : 0 ≤ d188 p :=
  nonnegative_ite (p 162) (nonnegative79 p) (nonnegative16 p)
def d189 (p : Pattern) : Int := if p 161 then d80 p else d188 p
theorem agree189 (p q : Pattern) (h : Agree support p q) : d189 p = d189 q := by
  simp only [d189, h 161 (by decide), agree80 p q h, agree188 p q h]
theorem nonnegative189 (p : Pattern) : 0 ≤ d189 p :=
  nonnegative_ite (p 161) (nonnegative80 p) (nonnegative188 p)
def d190 (p : Pattern) : Int := if p 247 then d12 p else d8 p
theorem agree190 (p q : Pattern) (h : Agree support p q) : d190 p = d190 q := by
  simp only [d190, h 247 (by decide), agree12 p q h, agree8 p q h]
theorem nonnegative190 (p : Pattern) : 0 ≤ d190 p :=
  nonnegative_ite (p 247) (nonnegative12 p) (nonnegative8 p)
def d191 (p : Pattern) : Int := if p 246 then d190 p else d8 p
theorem agree191 (p q : Pattern) (h : Agree support p q) : d191 p = d191 q := by
  simp only [d191, h 246 (by decide), agree190 p q h, agree8 p q h]
theorem nonnegative191 (p : Pattern) : 0 ≤ d191 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative8 p)
def d192 (p : Pattern) : Int := if p 204 then d12 p else d191 p
theorem agree192 (p q : Pattern) (h : Agree support p q) : d192 p = d192 q := by
  simp only [d192, h 204 (by decide), agree12 p q h, agree191 p q h]
theorem nonnegative192 (p : Pattern) : 0 ≤ d192 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative191 p)
def d193 (p : Pattern) : Int := if p 182 then d192 p else d191 p
theorem agree193 (p q : Pattern) (h : Agree support p q) : d193 p = d193 q := by
  simp only [d193, h 182 (by decide), agree192 p q h, agree191 p q h]
theorem nonnegative193 (p : Pattern) : 0 ≤ d193 p :=
  nonnegative_ite (p 182) (nonnegative192 p) (nonnegative191 p)
def d194 (p : Pattern) : Int := if p 163 then d193 p else d20 p
theorem agree194 (p q : Pattern) (h : Agree support p q) : d194 p = d194 q := by
  simp only [d194, h 163 (by decide), agree193 p q h, agree20 p q h]
theorem nonnegative194 (p : Pattern) : 0 ≤ d194 p :=
  nonnegative_ite (p 163) (nonnegative193 p) (nonnegative20 p)
def d195 (p : Pattern) : Int := if p 162 then d12 p else d194 p
theorem agree195 (p q : Pattern) (h : Agree support p q) : d195 p = d195 q := by
  simp only [d195, h 162 (by decide), agree12 p q h, agree194 p q h]
theorem nonnegative195 (p : Pattern) : 0 ≤ d195 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative194 p)
def d196 (p : Pattern) : Int := if p 161 then d12 p else d195 p
theorem agree196 (p q : Pattern) (h : Agree support p q) : d196 p = d196 q := by
  simp only [d196, h 161 (by decide), agree12 p q h, agree195 p q h]
theorem nonnegative196 (p : Pattern) : 0 ≤ d196 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative195 p)
def d197 (p : Pattern) : Int := if p 160 then d196 p else d189 p
theorem agree197 (p q : Pattern) (h : Agree support p q) : d197 p = d197 q := by
  simp only [d197, h 160 (by decide), agree196 p q h, agree189 p q h]
theorem nonnegative197 (p : Pattern) : 0 ≤ d197 p :=
  nonnegative_ite (p 160) (nonnegative196 p) (nonnegative189 p)
def d198 (p : Pattern) : Int := if p 163 then d62 p else d20 p
theorem agree198 (p q : Pattern) (h : Agree support p q) : d198 p = d198 q := by
  simp only [d198, h 163 (by decide), agree62 p q h, agree20 p q h]
theorem nonnegative198 (p : Pattern) : 0 ≤ d198 p :=
  nonnegative_ite (p 163) (nonnegative62 p) (nonnegative20 p)
def d199 (p : Pattern) : Int := if p 162 then d198 p else d53 p
theorem agree199 (p q : Pattern) (h : Agree support p q) : d199 p = d199 q := by
  simp only [d199, h 162 (by decide), agree198 p q h, agree53 p q h]
theorem nonnegative199 (p : Pattern) : 0 ≤ d199 p :=
  nonnegative_ite (p 162) (nonnegative198 p) (nonnegative53 p)
def d200 (p : Pattern) : Int := if p 161 then d84 p else d199 p
theorem agree200 (p q : Pattern) (h : Agree support p q) : d200 p = d200 q := by
  simp only [d200, h 161 (by decide), agree84 p q h, agree199 p q h]
theorem nonnegative200 (p : Pattern) : 0 ≤ d200 p :=
  nonnegative_ite (p 161) (nonnegative84 p) (nonnegative199 p)
def d201 (p : Pattern) : Int := if p 163 then d12 p else d193 p
theorem agree201 (p q : Pattern) (h : Agree support p q) : d201 p = d201 q := by
  simp only [d201, h 163 (by decide), agree12 p q h, agree193 p q h]
theorem nonnegative201 (p : Pattern) : 0 ≤ d201 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative193 p)
def d202 (p : Pattern) : Int := if p 162 then d12 p else d201 p
theorem agree202 (p q : Pattern) (h : Agree support p q) : d202 p = d202 q := by
  simp only [d202, h 162 (by decide), agree12 p q h, agree201 p q h]
theorem nonnegative202 (p : Pattern) : 0 ≤ d202 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative201 p)
def d203 (p : Pattern) : Int := if p 161 then d12 p else d202 p
theorem agree203 (p q : Pattern) (h : Agree support p q) : d203 p = d203 q := by
  simp only [d203, h 161 (by decide), agree12 p q h, agree202 p q h]
theorem nonnegative203 (p : Pattern) : 0 ≤ d203 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative202 p)
def d204 (p : Pattern) : Int := if p 160 then d203 p else d200 p
theorem agree204 (p q : Pattern) (h : Agree support p q) : d204 p = d204 q := by
  simp only [d204, h 160 (by decide), agree203 p q h, agree200 p q h]
theorem nonnegative204 (p : Pattern) : 0 ≤ d204 p :=
  nonnegative_ite (p 160) (nonnegative203 p) (nonnegative200 p)
def d205 (p : Pattern) : Int := if p 141 then d204 p else d197 p
theorem agree205 (p q : Pattern) (h : Agree support p q) : d205 p = d205 q := by
  simp only [d205, h 141 (by decide), agree204 p q h, agree197 p q h]
theorem nonnegative205 (p : Pattern) : 0 ≤ d205 p :=
  nonnegative_ite (p 141) (nonnegative204 p) (nonnegative197 p)
def d206 (p : Pattern) : Int := if p 138 then d205 p else d187 p
theorem agree206 (p q : Pattern) (h : Agree support p q) : d206 p = d206 q := by
  simp only [d206, h 138 (by decide), agree205 p q h, agree187 p q h]
theorem nonnegative206 (p : Pattern) : 0 ≤ d206 p :=
  nonnegative_ite (p 138) (nonnegative205 p) (nonnegative187 p)
def d207 (p : Pattern) : Int := if p 138 then d12 p else d205 p
theorem agree207 (p q : Pattern) (h : Agree support p q) : d207 p = d207 q := by
  simp only [d207, h 138 (by decide), agree12 p q h, agree205 p q h]
theorem nonnegative207 (p : Pattern) : 0 ≤ d207 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative205 p)
def d208 (p : Pattern) : Int := if p 116 then d207 p else d206 p
theorem agree208 (p q : Pattern) (h : Agree support p q) : d208 p = d208 q := by
  simp only [d208, h 116 (by decide), agree207 p q h, agree206 p q h]
theorem nonnegative208 (p : Pattern) : 0 ≤ d208 p :=
  nonnegative_ite (p 116) (nonnegative207 p) (nonnegative206 p)
def d209 (p : Pattern) : Int := if p 115 then d208 p else d98 p
theorem agree209 (p q : Pattern) (h : Agree support p q) : d209 p = d209 q := by
  simp only [d209, h 115 (by decide), agree208 p q h, agree98 p q h]
theorem nonnegative209 (p : Pattern) : 0 ≤ d209 p :=
  nonnegative_ite (p 115) (nonnegative208 p) (nonnegative98 p)
def d210 (p : Pattern) : Int := if p 71 then d209 p else d101 p
theorem agree210 (p q : Pattern) (h : Agree support p q) : d210 p = d210 q := by
  simp only [d210, h 71 (by decide), agree209 p q h, agree101 p q h]
theorem nonnegative210 (p : Pattern) : 0 ≤ d210 p :=
  nonnegative_ite (p 71) (nonnegative209 p) (nonnegative101 p)
def d211 (p : Pattern) : Int := if p 163 then d12 p else d109 p
theorem agree211 (p q : Pattern) (h : Agree support p q) : d211 p = d211 q := by
  simp only [d211, h 163 (by decide), agree12 p q h, agree109 p q h]
theorem nonnegative211 (p : Pattern) : 0 ≤ d211 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative109 p)
def d212 (p : Pattern) : Int := if p 162 then d211 p else d133 p
theorem agree212 (p q : Pattern) (h : Agree support p q) : d212 p = d212 q := by
  simp only [d212, h 162 (by decide), agree211 p q h, agree133 p q h]
theorem nonnegative212 (p : Pattern) : 0 ≤ d212 p :=
  nonnegative_ite (p 162) (nonnegative211 p) (nonnegative133 p)
def d213 (p : Pattern) : Int := if p 162 then d12 p else d211 p
theorem agree213 (p q : Pattern) (h : Agree support p q) : d213 p = d213 q := by
  simp only [d213, h 162 (by decide), agree12 p q h, agree211 p q h]
theorem nonnegative213 (p : Pattern) : 0 ≤ d213 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative211 p)
def d214 (p : Pattern) : Int := if p 161 then d213 p else d212 p
theorem agree214 (p q : Pattern) (h : Agree support p q) : d214 p = d214 q := by
  simp only [d214, h 161 (by decide), agree213 p q h, agree212 p q h]
theorem nonnegative214 (p : Pattern) : 0 ≤ d214 p :=
  nonnegative_ite (p 161) (nonnegative213 p) (nonnegative212 p)
def d215 (p : Pattern) : Int := if p 163 then d12 p else d125 p
theorem agree215 (p q : Pattern) (h : Agree support p q) : d215 p = d215 q := by
  simp only [d215, h 163 (by decide), agree12 p q h, agree125 p q h]
theorem nonnegative215 (p : Pattern) : 0 ≤ d215 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative125 p)
def d216 (p : Pattern) : Int := if p 162 then d215 p else d140 p
theorem agree216 (p q : Pattern) (h : Agree support p q) : d216 p = d216 q := by
  simp only [d216, h 162 (by decide), agree215 p q h, agree140 p q h]
theorem nonnegative216 (p : Pattern) : 0 ≤ d216 p :=
  nonnegative_ite (p 162) (nonnegative215 p) (nonnegative140 p)
def d217 (p : Pattern) : Int := if p 162 then d12 p else d215 p
theorem agree217 (p q : Pattern) (h : Agree support p q) : d217 p = d217 q := by
  simp only [d217, h 162 (by decide), agree12 p q h, agree215 p q h]
theorem nonnegative217 (p : Pattern) : 0 ≤ d217 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative215 p)
def d218 (p : Pattern) : Int := if p 161 then d217 p else d216 p
theorem agree218 (p q : Pattern) (h : Agree support p q) : d218 p = d218 q := by
  simp only [d218, h 161 (by decide), agree217 p q h, agree216 p q h]
theorem nonnegative218 (p : Pattern) : 0 ≤ d218 p :=
  nonnegative_ite (p 161) (nonnegative217 p) (nonnegative216 p)
def d219 (p : Pattern) : Int := if p 160 then d218 p else d214 p
theorem agree219 (p q : Pattern) (h : Agree support p q) : d219 p = d219 q := by
  simp only [d219, h 160 (by decide), agree218 p q h, agree214 p q h]
theorem nonnegative219 (p : Pattern) : 0 ≤ d219 p :=
  nonnegative_ite (p 160) (nonnegative218 p) (nonnegative214 p)
def d220 (p : Pattern) : Int := if p 141 then d219 p else d131 p
theorem agree220 (p q : Pattern) (h : Agree support p q) : d220 p = d220 q := by
  simp only [d220, h 141 (by decide), agree219 p q h, agree131 p q h]
theorem nonnegative220 (p : Pattern) : 0 ≤ d220 p :=
  nonnegative_ite (p 141) (nonnegative219 p) (nonnegative131 p)
def d221 (p : Pattern) : Int := if p 160 then d155 p else d214 p
theorem agree221 (p q : Pattern) (h : Agree support p q) : d221 p = d221 q := by
  simp only [d221, h 160 (by decide), agree155 p q h, agree214 p q h]
theorem nonnegative221 (p : Pattern) : 0 ≤ d221 p :=
  nonnegative_ite (p 160) (nonnegative155 p) (nonnegative214 p)
def d222 (p : Pattern) : Int := if p 141 then d221 p else d152 p
theorem agree222 (p q : Pattern) (h : Agree support p q) : d222 p = d222 q := by
  simp only [d222, h 141 (by decide), agree221 p q h, agree152 p q h]
theorem nonnegative222 (p : Pattern) : 0 ≤ d222 p :=
  nonnegative_ite (p 141) (nonnegative221 p) (nonnegative152 p)
def d223 (p : Pattern) : Int := if p 138 then d222 p else d220 p
theorem agree223 (p q : Pattern) (h : Agree support p q) : d223 p = d223 q := by
  simp only [d223, h 138 (by decide), agree222 p q h, agree220 p q h]
theorem nonnegative223 (p : Pattern) : 0 ≤ d223 p :=
  nonnegative_ite (p 138) (nonnegative222 p) (nonnegative220 p)
def d224 (p : Pattern) : Int := if p 138 then d162 p else d222 p
theorem agree224 (p q : Pattern) (h : Agree support p q) : d224 p = d224 q := by
  simp only [d224, h 138 (by decide), agree162 p q h, agree222 p q h]
theorem nonnegative224 (p : Pattern) : 0 ≤ d224 p :=
  nonnegative_ite (p 138) (nonnegative162 p) (nonnegative222 p)
def d225 (p : Pattern) : Int := if p 116 then d224 p else d223 p
theorem agree225 (p q : Pattern) (h : Agree support p q) : d225 p = d225 q := by
  simp only [d225, h 116 (by decide), agree224 p q h, agree223 p q h]
theorem nonnegative225 (p : Pattern) : 0 ≤ d225 p :=
  nonnegative_ite (p 116) (nonnegative224 p) (nonnegative223 p)
def d226 (p : Pattern) : Int := if p 182 then d121 p else d116 p
theorem agree226 (p q : Pattern) (h : Agree support p q) : d226 p = d226 q := by
  simp only [d226, h 182 (by decide), agree121 p q h, agree116 p q h]
theorem nonnegative226 (p : Pattern) : 0 ≤ d226 p :=
  nonnegative_ite (p 182) (nonnegative121 p) (nonnegative116 p)
def d227 (p : Pattern) : Int := if p 163 then d226 p else d132 p
theorem agree227 (p q : Pattern) (h : Agree support p q) : d227 p = d227 q := by
  simp only [d227, h 163 (by decide), agree226 p q h, agree132 p q h]
theorem nonnegative227 (p : Pattern) : 0 ≤ d227 p :=
  nonnegative_ite (p 163) (nonnegative226 p) (nonnegative132 p)
def d228 (p : Pattern) : Int := if p 162 then d215 p else d227 p
theorem agree228 (p q : Pattern) (h : Agree support p q) : d228 p = d228 q := by
  simp only [d228, h 162 (by decide), agree215 p q h, agree227 p q h]
theorem nonnegative228 (p : Pattern) : 0 ≤ d228 p :=
  nonnegative_ite (p 162) (nonnegative215 p) (nonnegative227 p)
def d229 (p : Pattern) : Int := if p 182 then d12 p else d120 p
theorem agree229 (p q : Pattern) (h : Agree support p q) : d229 p = d229 q := by
  simp only [d229, h 182 (by decide), agree12 p q h, agree120 p q h]
theorem nonnegative229 (p : Pattern) : 0 ≤ d229 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative120 p)
def d230 (p : Pattern) : Int := if p 163 then d12 p else d229 p
theorem agree230 (p q : Pattern) (h : Agree support p q) : d230 p = d230 q := by
  simp only [d230, h 163 (by decide), agree12 p q h, agree229 p q h]
theorem nonnegative230 (p : Pattern) : 0 ≤ d230 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative229 p)
def d231 (p : Pattern) : Int := if p 162 then d12 p else d230 p
theorem agree231 (p q : Pattern) (h : Agree support p q) : d231 p = d231 q := by
  simp only [d231, h 162 (by decide), agree12 p q h, agree230 p q h]
theorem nonnegative231 (p : Pattern) : 0 ≤ d231 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative230 p)
def d232 (p : Pattern) : Int := if p 161 then d231 p else d228 p
theorem agree232 (p q : Pattern) (h : Agree support p q) : d232 p = d232 q := by
  simp only [d232, h 161 (by decide), agree231 p q h, agree228 p q h]
theorem nonnegative232 (p : Pattern) : 0 ≤ d232 p :=
  nonnegative_ite (p 161) (nonnegative231 p) (nonnegative228 p)
def d233 (p : Pattern) : Int := if p 160 then d232 p else d114 p
theorem agree233 (p q : Pattern) (h : Agree support p q) : d233 p = d233 q := by
  simp only [d233, h 160 (by decide), agree232 p q h, agree114 p q h]
theorem nonnegative233 (p : Pattern) : 0 ≤ d233 p :=
  nonnegative_ite (p 160) (nonnegative232 p) (nonnegative114 p)
def d234 (p : Pattern) : Int := if p 182 then d121 p else d107 p
theorem agree234 (p q : Pattern) (h : Agree support p q) : d234 p = d234 q := by
  simp only [d234, h 182 (by decide), agree121 p q h, agree107 p q h]
theorem nonnegative234 (p : Pattern) : 0 ≤ d234 p :=
  nonnegative_ite (p 182) (nonnegative121 p) (nonnegative107 p)
def d235 (p : Pattern) : Int := if p 163 then d125 p else d234 p
theorem agree235 (p q : Pattern) (h : Agree support p q) : d235 p = d235 q := by
  simp only [d235, h 163 (by decide), agree125 p q h, agree234 p q h]
theorem nonnegative235 (p : Pattern) : 0 ≤ d235 p :=
  nonnegative_ite (p 163) (nonnegative125 p) (nonnegative234 p)
def d236 (p : Pattern) : Int := if p 162 then d230 p else d235 p
theorem agree236 (p q : Pattern) (h : Agree support p q) : d236 p = d236 q := by
  simp only [d236, h 162 (by decide), agree230 p q h, agree235 p q h]
theorem nonnegative236 (p : Pattern) : 0 ≤ d236 p :=
  nonnegative_ite (p 162) (nonnegative230 p) (nonnegative235 p)
def d237 (p : Pattern) : Int := if p 162 then d12 p else d49 p
theorem agree237 (p q : Pattern) (h : Agree support p q) : d237 p = d237 q := by
  simp only [d237, h 162 (by decide), agree12 p q h, agree49 p q h]
theorem nonnegative237 (p : Pattern) : 0 ≤ d237 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative49 p)
def d238 (p : Pattern) : Int := if p 161 then d237 p else d236 p
theorem agree238 (p q : Pattern) (h : Agree support p q) : d238 p = d238 q := by
  simp only [d238, h 161 (by decide), agree237 p q h, agree236 p q h]
theorem nonnegative238 (p : Pattern) : 0 ≤ d238 p :=
  nonnegative_ite (p 161) (nonnegative237 p) (nonnegative236 p)
def d239 (p : Pattern) : Int := if p 160 then d238 p else d214 p
theorem agree239 (p q : Pattern) (h : Agree support p q) : d239 p = d239 q := by
  simp only [d239, h 160 (by decide), agree238 p q h, agree214 p q h]
theorem nonnegative239 (p : Pattern) : 0 ≤ d239 p :=
  nonnegative_ite (p 160) (nonnegative238 p) (nonnegative214 p)
end NetHack.Sokoban22Refined85
