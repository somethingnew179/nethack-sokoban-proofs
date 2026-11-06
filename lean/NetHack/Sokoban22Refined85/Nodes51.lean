/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes50
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6120 (p : Pattern) : Int := if p 163 then d6113 p else d6103 p
theorem agree6120 (p q : Pattern) (h : Agree support p q) : d6120 p = d6120 q := by
  simp only [d6120, h 163 (by decide), agree6113 p q h, agree6103 p q h]
theorem nonnegative6120 (p : Pattern) : 0 ≤ d6120 p :=
  nonnegative_ite (p 163) (nonnegative6113 p) (nonnegative6103 p)
def d6121 (p : Pattern) : Int := if p 163 then d6109 p else d6105 p
theorem agree6121 (p q : Pattern) (h : Agree support p q) : d6121 p = d6121 q := by
  simp only [d6121, h 163 (by decide), agree6109 p q h, agree6105 p q h]
theorem nonnegative6121 (p : Pattern) : 0 ≤ d6121 p :=
  nonnegative_ite (p 163) (nonnegative6109 p) (nonnegative6105 p)
def d6122 (p : Pattern) : Int := if p 162 then d6121 p else d6120 p
theorem agree6122 (p q : Pattern) (h : Agree support p q) : d6122 p = d6122 q := by
  simp only [d6122, h 162 (by decide), agree6121 p q h, agree6120 p q h]
theorem nonnegative6122 (p : Pattern) : 0 ≤ d6122 p :=
  nonnegative_ite (p 162) (nonnegative6121 p) (nonnegative6120 p)
def d6123 (p : Pattern) : Int := if p 163 then d6083 p else d6105 p
theorem agree6123 (p q : Pattern) (h : Agree support p q) : d6123 p = d6123 q := by
  simp only [d6123, h 163 (by decide), agree6083 p q h, agree6105 p q h]
theorem nonnegative6123 (p : Pattern) : 0 ≤ d6123 p :=
  nonnegative_ite (p 163) (nonnegative6083 p) (nonnegative6105 p)
def d6124 (p : Pattern) : Int := if p 162 then d6087 p else d6123 p
theorem agree6124 (p q : Pattern) (h : Agree support p q) : d6124 p = d6124 q := by
  simp only [d6124, h 162 (by decide), agree6087 p q h, agree6123 p q h]
theorem nonnegative6124 (p : Pattern) : 0 ≤ d6124 p :=
  nonnegative_ite (p 162) (nonnegative6087 p) (nonnegative6123 p)
def d6125 (p : Pattern) : Int := if p 161 then d6124 p else d6122 p
theorem agree6125 (p q : Pattern) (h : Agree support p q) : d6125 p = d6125 q := by
  simp only [d6125, h 161 (by decide), agree6124 p q h, agree6122 p q h]
theorem nonnegative6125 (p : Pattern) : 0 ≤ d6125 p :=
  nonnegative_ite (p 161) (nonnegative6124 p) (nonnegative6122 p)
def d6126 (p : Pattern) : Int := if p 163 then d12 p else d6115 p
theorem agree6126 (p q : Pattern) (h : Agree support p q) : d6126 p = d6126 q := by
  simp only [d6126, h 163 (by decide), agree12 p q h, agree6115 p q h]
theorem nonnegative6126 (p : Pattern) : 0 ≤ d6126 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6115 p)
def d6127 (p : Pattern) : Int := if p 162 then d12 p else d6126 p
theorem agree6127 (p q : Pattern) (h : Agree support p q) : d6127 p = d6127 q := by
  simp only [d6127, h 162 (by decide), agree12 p q h, agree6126 p q h]
theorem nonnegative6127 (p : Pattern) : 0 ≤ d6127 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6126 p)
def d6128 (p : Pattern) : Int := if p 161 then d12 p else d6127 p
theorem agree6128 (p q : Pattern) (h : Agree support p q) : d6128 p = d6128 q := by
  simp only [d6128, h 161 (by decide), agree12 p q h, agree6127 p q h]
theorem nonnegative6128 (p : Pattern) : 0 ≤ d6128 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6127 p)
def d6129 (p : Pattern) : Int := if p 160 then d6128 p else d6125 p
theorem agree6129 (p q : Pattern) (h : Agree support p q) : d6129 p = d6129 q := by
  simp only [d6129, h 160 (by decide), agree6128 p q h, agree6125 p q h]
theorem nonnegative6129 (p : Pattern) : 0 ≤ d6129 p :=
  nonnegative_ite (p 160) (nonnegative6128 p) (nonnegative6125 p)
def d6130 (p : Pattern) : Int := if p 141 then d6129 p else d6119 p
theorem agree6130 (p q : Pattern) (h : Agree support p q) : d6130 p = d6130 q := by
  simp only [d6130, h 141 (by decide), agree6129 p q h, agree6119 p q h]
theorem nonnegative6130 (p : Pattern) : 0 ≤ d6130 p :=
  nonnegative_ite (p 141) (nonnegative6129 p) (nonnegative6119 p)
def d6131 (p : Pattern) : Int := if p 138 then d6130 p else d6101 p
theorem agree6131 (p q : Pattern) (h : Agree support p q) : d6131 p = d6131 q := by
  simp only [d6131, h 138 (by decide), agree6130 p q h, agree6101 p q h]
theorem nonnegative6131 (p : Pattern) : 0 ≤ d6131 p :=
  nonnegative_ite (p 138) (nonnegative6130 p) (nonnegative6101 p)
def d6132 (p : Pattern) : Int := if p 163 then d6086 p else d6109 p
theorem agree6132 (p q : Pattern) (h : Agree support p q) : d6132 p = d6132 q := by
  simp only [d6132, h 163 (by decide), agree6086 p q h, agree6109 p q h]
theorem nonnegative6132 (p : Pattern) : 0 ≤ d6132 p :=
  nonnegative_ite (p 163) (nonnegative6086 p) (nonnegative6109 p)
def d6133 (p : Pattern) : Int := if p 162 then d6087 p else d6132 p
theorem agree6133 (p q : Pattern) (h : Agree support p q) : d6133 p = d6133 q := by
  simp only [d6133, h 162 (by decide), agree6087 p q h, agree6132 p q h]
theorem nonnegative6133 (p : Pattern) : 0 ≤ d6133 p :=
  nonnegative_ite (p 162) (nonnegative6087 p) (nonnegative6132 p)
def d6134 (p : Pattern) : Int := if p 162 then d12 p else d6087 p
theorem agree6134 (p q : Pattern) (h : Agree support p q) : d6134 p = d6134 q := by
  simp only [d6134, h 162 (by decide), agree12 p q h, agree6087 p q h]
theorem nonnegative6134 (p : Pattern) : 0 ≤ d6134 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6087 p)
def d6135 (p : Pattern) : Int := if p 161 then d6134 p else d6133 p
theorem agree6135 (p q : Pattern) (h : Agree support p q) : d6135 p = d6135 q := by
  simp only [d6135, h 161 (by decide), agree6134 p q h, agree6133 p q h]
theorem nonnegative6135 (p : Pattern) : 0 ≤ d6135 p :=
  nonnegative_ite (p 161) (nonnegative6134 p) (nonnegative6133 p)
def d6136 (p : Pattern) : Int := if p 161 then d12 p else d6134 p
theorem agree6136 (p q : Pattern) (h : Agree support p q) : d6136 p = d6136 q := by
  simp only [d6136, h 161 (by decide), agree12 p q h, agree6134 p q h]
theorem nonnegative6136 (p : Pattern) : 0 ≤ d6136 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6134 p)
def d6137 (p : Pattern) : Int := if p 160 then d6136 p else d6135 p
theorem agree6137 (p q : Pattern) (h : Agree support p q) : d6137 p = d6137 q := by
  simp only [d6137, h 160 (by decide), agree6136 p q h, agree6135 p q h]
theorem nonnegative6137 (p : Pattern) : 0 ≤ d6137 p :=
  nonnegative_ite (p 160) (nonnegative6136 p) (nonnegative6135 p)
def d6138 (p : Pattern) : Int := if p 160 then d12 p else d6136 p
theorem agree6138 (p q : Pattern) (h : Agree support p q) : d6138 p = d6138 q := by
  simp only [d6138, h 160 (by decide), agree12 p q h, agree6136 p q h]
theorem nonnegative6138 (p : Pattern) : 0 ≤ d6138 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative6136 p)
def d6139 (p : Pattern) : Int := if p 141 then d6138 p else d6137 p
theorem agree6139 (p q : Pattern) (h : Agree support p q) : d6139 p = d6139 q := by
  simp only [d6139, h 141 (by decide), agree6138 p q h, agree6137 p q h]
theorem nonnegative6139 (p : Pattern) : 0 ≤ d6139 p :=
  nonnegative_ite (p 141) (nonnegative6138 p) (nonnegative6137 p)
def d6140 (p : Pattern) : Int := if p 138 then d6139 p else d6130 p
theorem agree6140 (p q : Pattern) (h : Agree support p q) : d6140 p = d6140 q := by
  simp only [d6140, h 138 (by decide), agree6139 p q h, agree6130 p q h]
theorem nonnegative6140 (p : Pattern) : 0 ≤ d6140 p :=
  nonnegative_ite (p 138) (nonnegative6139 p) (nonnegative6130 p)
def d6141 (p : Pattern) : Int := if p 116 then d6140 p else d6131 p
theorem agree6141 (p q : Pattern) (h : Agree support p q) : d6141 p = d6141 q := by
  simp only [d6141, h 116 (by decide), agree6140 p q h, agree6131 p q h]
theorem nonnegative6141 (p : Pattern) : 0 ≤ d6141 p :=
  nonnegative_ite (p 116) (nonnegative6140 p) (nonnegative6131 p)
def d6142 (p : Pattern) : Int := if p 138 then d12 p else d6130 p
theorem agree6142 (p q : Pattern) (h : Agree support p q) : d6142 p = d6142 q := by
  simp only [d6142, h 138 (by decide), agree12 p q h, agree6130 p q h]
theorem nonnegative6142 (p : Pattern) : 0 ≤ d6142 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6130 p)
def d6143 (p : Pattern) : Int := if p 116 then d6142 p else d6131 p
theorem agree6143 (p q : Pattern) (h : Agree support p q) : d6143 p = d6143 q := by
  simp only [d6143, h 116 (by decide), agree6142 p q h, agree6131 p q h]
theorem nonnegative6143 (p : Pattern) : 0 ≤ d6143 p :=
  nonnegative_ite (p 116) (nonnegative6142 p) (nonnegative6131 p)
def d6144 (p : Pattern) : Int := if p 115 then d6143 p else d6141 p
theorem agree6144 (p q : Pattern) (h : Agree support p q) : d6144 p = d6144 q := by
  simp only [d6144, h 115 (by decide), agree6143 p q h, agree6141 p q h]
theorem nonnegative6144 (p : Pattern) : 0 ≤ d6144 p :=
  nonnegative_ite (p 115) (nonnegative6143 p) (nonnegative6141 p)
def d6145 (p : Pattern) : Int := if p 204 then d1940 p else d103 p
theorem agree6145 (p q : Pattern) (h : Agree support p q) : d6145 p = d6145 q := by
  simp only [d6145, h 204 (by decide), agree1940 p q h, agree103 p q h]
theorem nonnegative6145 (p : Pattern) : 0 ≤ d6145 p :=
  nonnegative_ite (p 204) (nonnegative1940 p) (nonnegative103 p)
def d6146 (p : Pattern) : Int := if p 204 then d12 p else d1873 p
theorem agree6146 (p q : Pattern) (h : Agree support p q) : d6146 p = d6146 q := by
  simp only [d6146, h 204 (by decide), agree12 p q h, agree1873 p q h]
theorem nonnegative6146 (p : Pattern) : 0 ≤ d6146 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1873 p)
def d6147 (p : Pattern) : Int := if p 182 then d6146 p else d6145 p
theorem agree6147 (p q : Pattern) (h : Agree support p q) : d6147 p = d6147 q := by
  simp only [d6147, h 182 (by decide), agree6146 p q h, agree6145 p q h]
theorem nonnegative6147 (p : Pattern) : 0 ≤ d6147 p :=
  nonnegative_ite (p 182) (nonnegative6146 p) (nonnegative6145 p)
def d6148 (p : Pattern) : Int := if p 204 then d1964 p else d107 p
theorem agree6148 (p q : Pattern) (h : Agree support p q) : d6148 p = d6148 q := by
  simp only [d6148, h 204 (by decide), agree1964 p q h, agree107 p q h]
theorem nonnegative6148 (p : Pattern) : 0 ≤ d6148 p :=
  nonnegative_ite (p 204) (nonnegative1964 p) (nonnegative107 p)
def d6149 (p : Pattern) : Int := if p 204 then d12 p else d1881 p
theorem agree6149 (p q : Pattern) (h : Agree support p q) : d6149 p = d6149 q := by
  simp only [d6149, h 204 (by decide), agree12 p q h, agree1881 p q h]
theorem nonnegative6149 (p : Pattern) : 0 ≤ d6149 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1881 p)
def d6150 (p : Pattern) : Int := if p 182 then d6149 p else d6148 p
theorem agree6150 (p q : Pattern) (h : Agree support p q) : d6150 p = d6150 q := by
  simp only [d6150, h 182 (by decide), agree6149 p q h, agree6148 p q h]
theorem nonnegative6150 (p : Pattern) : 0 ≤ d6150 p :=
  nonnegative_ite (p 182) (nonnegative6149 p) (nonnegative6148 p)
def d6151 (p : Pattern) : Int := if p 163 then d6150 p else d6147 p
theorem agree6151 (p q : Pattern) (h : Agree support p q) : d6151 p = d6151 q := by
  simp only [d6151, h 163 (by decide), agree6150 p q h, agree6147 p q h]
theorem nonnegative6151 (p : Pattern) : 0 ≤ d6151 p :=
  nonnegative_ite (p 163) (nonnegative6150 p) (nonnegative6147 p)
def d6152 (p : Pattern) : Int := if p 162 then d6151 p else d6147 p
theorem agree6152 (p q : Pattern) (h : Agree support p q) : d6152 p = d6152 q := by
  simp only [d6152, h 162 (by decide), agree6151 p q h, agree6147 p q h]
theorem nonnegative6152 (p : Pattern) : 0 ≤ d6152 p :=
  nonnegative_ite (p 162) (nonnegative6151 p) (nonnegative6147 p)
def d6153 (p : Pattern) : Int := if p 163 then d12 p else d6083 p
theorem agree6153 (p q : Pattern) (h : Agree support p q) : d6153 p = d6153 q := by
  simp only [d6153, h 163 (by decide), agree12 p q h, agree6083 p q h]
theorem nonnegative6153 (p : Pattern) : 0 ≤ d6153 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6083 p)
def d6154 (p : Pattern) : Int := if p 162 then d6153 p else d6151 p
theorem agree6154 (p q : Pattern) (h : Agree support p q) : d6154 p = d6154 q := by
  simp only [d6154, h 162 (by decide), agree6153 p q h, agree6151 p q h]
theorem nonnegative6154 (p : Pattern) : 0 ≤ d6154 p :=
  nonnegative_ite (p 162) (nonnegative6153 p) (nonnegative6151 p)
def d6155 (p : Pattern) : Int := if p 161 then d6154 p else d6152 p
theorem agree6155 (p q : Pattern) (h : Agree support p q) : d6155 p = d6155 q := by
  simp only [d6155, h 161 (by decide), agree6154 p q h, agree6152 p q h]
theorem nonnegative6155 (p : Pattern) : 0 ≤ d6155 p :=
  nonnegative_ite (p 161) (nonnegative6154 p) (nonnegative6152 p)
def d6156 (p : Pattern) : Int := if p 204 then d12 p else d1895 p
theorem agree6156 (p q : Pattern) (h : Agree support p q) : d6156 p = d6156 q := by
  simp only [d6156, h 204 (by decide), agree12 p q h, agree1895 p q h]
theorem nonnegative6156 (p : Pattern) : 0 ≤ d6156 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1895 p)
def d6157 (p : Pattern) : Int := if p 182 then d6156 p else d6145 p
theorem agree6157 (p q : Pattern) (h : Agree support p q) : d6157 p = d6157 q := by
  simp only [d6157, h 182 (by decide), agree6156 p q h, agree6145 p q h]
theorem nonnegative6157 (p : Pattern) : 0 ≤ d6157 p :=
  nonnegative_ite (p 182) (nonnegative6156 p) (nonnegative6145 p)
def d6158 (p : Pattern) : Int := if p 204 then d12 p else d1903 p
theorem agree6158 (p q : Pattern) (h : Agree support p q) : d6158 p = d6158 q := by
  simp only [d6158, h 204 (by decide), agree12 p q h, agree1903 p q h]
theorem nonnegative6158 (p : Pattern) : 0 ≤ d6158 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1903 p)
def d6159 (p : Pattern) : Int := if p 182 then d6158 p else d6145 p
theorem agree6159 (p q : Pattern) (h : Agree support p q) : d6159 p = d6159 q := by
  simp only [d6159, h 182 (by decide), agree6158 p q h, agree6145 p q h]
theorem nonnegative6159 (p : Pattern) : 0 ≤ d6159 p :=
  nonnegative_ite (p 182) (nonnegative6158 p) (nonnegative6145 p)
def d6160 (p : Pattern) : Int := if p 163 then d6159 p else d6157 p
theorem agree6160 (p q : Pattern) (h : Agree support p q) : d6160 p = d6160 q := by
  simp only [d6160, h 163 (by decide), agree6159 p q h, agree6157 p q h]
theorem nonnegative6160 (p : Pattern) : 0 ≤ d6160 p :=
  nonnegative_ite (p 163) (nonnegative6159 p) (nonnegative6157 p)
def d6161 (p : Pattern) : Int := if p 182 then d12 p else d6145 p
theorem agree6161 (p q : Pattern) (h : Agree support p q) : d6161 p = d6161 q := by
  simp only [d6161, h 182 (by decide), agree12 p q h, agree6145 p q h]
theorem nonnegative6161 (p : Pattern) : 0 ≤ d6161 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6145 p)
def d6162 (p : Pattern) : Int := if p 182 then d12 p else d6148 p
theorem agree6162 (p q : Pattern) (h : Agree support p q) : d6162 p = d6162 q := by
  simp only [d6162, h 182 (by decide), agree12 p q h, agree6148 p q h]
theorem nonnegative6162 (p : Pattern) : 0 ≤ d6162 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6148 p)
def d6163 (p : Pattern) : Int := if p 163 then d6162 p else d6161 p
theorem agree6163 (p q : Pattern) (h : Agree support p q) : d6163 p = d6163 q := by
  simp only [d6163, h 163 (by decide), agree6162 p q h, agree6161 p q h]
theorem nonnegative6163 (p : Pattern) : 0 ≤ d6163 p :=
  nonnegative_ite (p 163) (nonnegative6162 p) (nonnegative6161 p)
def d6164 (p : Pattern) : Int := if p 162 then d6163 p else d6160 p
theorem agree6164 (p q : Pattern) (h : Agree support p q) : d6164 p = d6164 q := by
  simp only [d6164, h 162 (by decide), agree6163 p q h, agree6160 p q h]
theorem nonnegative6164 (p : Pattern) : 0 ≤ d6164 p :=
  nonnegative_ite (p 162) (nonnegative6163 p) (nonnegative6160 p)
def d6165 (p : Pattern) : Int := if p 163 then d12 p else d6094 p
theorem agree6165 (p q : Pattern) (h : Agree support p q) : d6165 p = d6165 q := by
  simp only [d6165, h 163 (by decide), agree12 p q h, agree6094 p q h]
theorem nonnegative6165 (p : Pattern) : 0 ≤ d6165 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6094 p)
def d6166 (p : Pattern) : Int := if p 162 then d6165 p else d6163 p
theorem agree6166 (p q : Pattern) (h : Agree support p q) : d6166 p = d6166 q := by
  simp only [d6166, h 162 (by decide), agree6165 p q h, agree6163 p q h]
theorem nonnegative6166 (p : Pattern) : 0 ≤ d6166 p :=
  nonnegative_ite (p 162) (nonnegative6165 p) (nonnegative6163 p)
def d6167 (p : Pattern) : Int := if p 161 then d6166 p else d6164 p
theorem agree6167 (p q : Pattern) (h : Agree support p q) : d6167 p = d6167 q := by
  simp only [d6167, h 161 (by decide), agree6166 p q h, agree6164 p q h]
theorem nonnegative6167 (p : Pattern) : 0 ≤ d6167 p :=
  nonnegative_ite (p 161) (nonnegative6166 p) (nonnegative6164 p)
def d6168 (p : Pattern) : Int := if p 160 then d6167 p else d6155 p
theorem agree6168 (p q : Pattern) (h : Agree support p q) : d6168 p = d6168 q := by
  simp only [d6168, h 160 (by decide), agree6167 p q h, agree6155 p q h]
theorem nonnegative6168 (p : Pattern) : 0 ≤ d6168 p :=
  nonnegative_ite (p 160) (nonnegative6167 p) (nonnegative6155 p)
def d6169 (p : Pattern) : Int := if p 204 then d1895 p else d116 p
theorem agree6169 (p q : Pattern) (h : Agree support p q) : d6169 p = d6169 q := by
  simp only [d6169, h 204 (by decide), agree1895 p q h, agree116 p q h]
theorem nonnegative6169 (p : Pattern) : 0 ≤ d6169 p :=
  nonnegative_ite (p 204) (nonnegative1895 p) (nonnegative116 p)
def d6170 (p : Pattern) : Int := if p 204 then d12 p else d1919 p
theorem agree6170 (p q : Pattern) (h : Agree support p q) : d6170 p = d6170 q := by
  simp only [d6170, h 204 (by decide), agree12 p q h, agree1919 p q h]
theorem nonnegative6170 (p : Pattern) : 0 ≤ d6170 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1919 p)
def d6171 (p : Pattern) : Int := if p 182 then d6170 p else d6169 p
theorem agree6171 (p q : Pattern) (h : Agree support p q) : d6171 p = d6171 q := by
  simp only [d6171, h 182 (by decide), agree6170 p q h, agree6169 p q h]
theorem nonnegative6171 (p : Pattern) : 0 ≤ d6171 p :=
  nonnegative_ite (p 182) (nonnegative6170 p) (nonnegative6169 p)
def d6172 (p : Pattern) : Int := if p 163 then d6171 p else d6147 p
theorem agree6172 (p q : Pattern) (h : Agree support p q) : d6172 p = d6172 q := by
  simp only [d6172, h 163 (by decide), agree6171 p q h, agree6147 p q h]
theorem nonnegative6172 (p : Pattern) : 0 ≤ d6172 p :=
  nonnegative_ite (p 163) (nonnegative6171 p) (nonnegative6147 p)
def d6173 (p : Pattern) : Int := if p 163 then d6083 p else d6150 p
theorem agree6173 (p q : Pattern) (h : Agree support p q) : d6173 p = d6173 q := by
  simp only [d6173, h 163 (by decide), agree6083 p q h, agree6150 p q h]
theorem nonnegative6173 (p : Pattern) : 0 ≤ d6173 p :=
  nonnegative_ite (p 163) (nonnegative6083 p) (nonnegative6150 p)
def d6174 (p : Pattern) : Int := if p 162 then d6173 p else d6172 p
theorem agree6174 (p q : Pattern) (h : Agree support p q) : d6174 p = d6174 q := by
  simp only [d6174, h 162 (by decide), agree6173 p q h, agree6172 p q h]
theorem nonnegative6174 (p : Pattern) : 0 ≤ d6174 p :=
  nonnegative_ite (p 162) (nonnegative6173 p) (nonnegative6172 p)
def d6175 (p : Pattern) : Int := if p 163 then d6086 p else d6150 p
theorem agree6175 (p q : Pattern) (h : Agree support p q) : d6175 p = d6175 q := by
  simp only [d6175, h 163 (by decide), agree6086 p q h, agree6150 p q h]
theorem nonnegative6175 (p : Pattern) : 0 ≤ d6175 p :=
  nonnegative_ite (p 163) (nonnegative6086 p) (nonnegative6150 p)
def d6176 (p : Pattern) : Int := if p 162 then d12 p else d6175 p
theorem agree6176 (p q : Pattern) (h : Agree support p q) : d6176 p = d6176 q := by
  simp only [d6176, h 162 (by decide), agree12 p q h, agree6175 p q h]
theorem nonnegative6176 (p : Pattern) : 0 ≤ d6176 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6175 p)
def d6177 (p : Pattern) : Int := if p 161 then d6176 p else d6174 p
theorem agree6177 (p q : Pattern) (h : Agree support p q) : d6177 p = d6177 q := by
  simp only [d6177, h 161 (by decide), agree6176 p q h, agree6174 p q h]
theorem nonnegative6177 (p : Pattern) : 0 ≤ d6177 p :=
  nonnegative_ite (p 161) (nonnegative6176 p) (nonnegative6174 p)
def d6178 (p : Pattern) : Int := if p 182 then d12 p else d6169 p
theorem agree6178 (p q : Pattern) (h : Agree support p q) : d6178 p = d6178 q := by
  simp only [d6178, h 182 (by decide), agree12 p q h, agree6169 p q h]
theorem nonnegative6178 (p : Pattern) : 0 ≤ d6178 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6169 p)
def d6179 (p : Pattern) : Int := if p 163 then d6178 p else d6159 p
theorem agree6179 (p q : Pattern) (h : Agree support p q) : d6179 p = d6179 q := by
  simp only [d6179, h 163 (by decide), agree6178 p q h, agree6159 p q h]
theorem nonnegative6179 (p : Pattern) : 0 ≤ d6179 p :=
  nonnegative_ite (p 163) (nonnegative6178 p) (nonnegative6159 p)
def d6180 (p : Pattern) : Int := if p 163 then d6094 p else d6162 p
theorem agree6180 (p q : Pattern) (h : Agree support p q) : d6180 p = d6180 q := by
  simp only [d6180, h 163 (by decide), agree6094 p q h, agree6162 p q h]
theorem nonnegative6180 (p : Pattern) : 0 ≤ d6180 p :=
  nonnegative_ite (p 163) (nonnegative6094 p) (nonnegative6162 p)
def d6181 (p : Pattern) : Int := if p 162 then d6180 p else d6179 p
theorem agree6181 (p q : Pattern) (h : Agree support p q) : d6181 p = d6181 q := by
  simp only [d6181, h 162 (by decide), agree6180 p q h, agree6179 p q h]
theorem nonnegative6181 (p : Pattern) : 0 ≤ d6181 p :=
  nonnegative_ite (p 162) (nonnegative6180 p) (nonnegative6179 p)
def d6182 (p : Pattern) : Int := if p 163 then d6096 p else d6162 p
theorem agree6182 (p q : Pattern) (h : Agree support p q) : d6182 p = d6182 q := by
  simp only [d6182, h 163 (by decide), agree6096 p q h, agree6162 p q h]
theorem nonnegative6182 (p : Pattern) : 0 ≤ d6182 p :=
  nonnegative_ite (p 163) (nonnegative6096 p) (nonnegative6162 p)
def d6183 (p : Pattern) : Int := if p 162 then d12 p else d6182 p
theorem agree6183 (p q : Pattern) (h : Agree support p q) : d6183 p = d6183 q := by
  simp only [d6183, h 162 (by decide), agree12 p q h, agree6182 p q h]
theorem nonnegative6183 (p : Pattern) : 0 ≤ d6183 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6182 p)
def d6184 (p : Pattern) : Int := if p 161 then d6183 p else d6181 p
theorem agree6184 (p q : Pattern) (h : Agree support p q) : d6184 p = d6184 q := by
  simp only [d6184, h 161 (by decide), agree6183 p q h, agree6181 p q h]
theorem nonnegative6184 (p : Pattern) : 0 ≤ d6184 p :=
  nonnegative_ite (p 161) (nonnegative6183 p) (nonnegative6181 p)
def d6185 (p : Pattern) : Int := if p 160 then d6184 p else d6177 p
theorem agree6185 (p q : Pattern) (h : Agree support p q) : d6185 p = d6185 q := by
  simp only [d6185, h 160 (by decide), agree6184 p q h, agree6177 p q h]
theorem nonnegative6185 (p : Pattern) : 0 ≤ d6185 p :=
  nonnegative_ite (p 160) (nonnegative6184 p) (nonnegative6177 p)
def d6186 (p : Pattern) : Int := if p 141 then d6185 p else d6168 p
theorem agree6186 (p q : Pattern) (h : Agree support p q) : d6186 p = d6186 q := by
  simp only [d6186, h 141 (by decide), agree6185 p q h, agree6168 p q h]
theorem nonnegative6186 (p : Pattern) : 0 ≤ d6186 p :=
  nonnegative_ite (p 141) (nonnegative6185 p) (nonnegative6168 p)
def d6187 (p : Pattern) : Int := if p 204 then d12 p else d1940 p
theorem agree6187 (p q : Pattern) (h : Agree support p q) : d6187 p = d6187 q := by
  simp only [d6187, h 204 (by decide), agree12 p q h, agree1940 p q h]
theorem nonnegative6187 (p : Pattern) : 0 ≤ d6187 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1940 p)
def d6188 (p : Pattern) : Int := if p 182 then d6187 p else d6145 p
theorem agree6188 (p q : Pattern) (h : Agree support p q) : d6188 p = d6188 q := by
  simp only [d6188, h 182 (by decide), agree6187 p q h, agree6145 p q h]
theorem nonnegative6188 (p : Pattern) : 0 ≤ d6188 p :=
  nonnegative_ite (p 182) (nonnegative6187 p) (nonnegative6145 p)
def d6189 (p : Pattern) : Int := if p 204 then d12 p else d1964 p
theorem agree6189 (p q : Pattern) (h : Agree support p q) : d6189 p = d6189 q := by
  simp only [d6189, h 204 (by decide), agree12 p q h, agree1964 p q h]
theorem nonnegative6189 (p : Pattern) : 0 ≤ d6189 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1964 p)
def d6190 (p : Pattern) : Int := if p 182 then d6189 p else d6148 p
theorem agree6190 (p q : Pattern) (h : Agree support p q) : d6190 p = d6190 q := by
  simp only [d6190, h 182 (by decide), agree6189 p q h, agree6148 p q h]
theorem nonnegative6190 (p : Pattern) : 0 ≤ d6190 p :=
  nonnegative_ite (p 182) (nonnegative6189 p) (nonnegative6148 p)
def d6191 (p : Pattern) : Int := if p 163 then d6190 p else d6188 p
theorem agree6191 (p q : Pattern) (h : Agree support p q) : d6191 p = d6191 q := by
  simp only [d6191, h 163 (by decide), agree6190 p q h, agree6188 p q h]
theorem nonnegative6191 (p : Pattern) : 0 ≤ d6191 p :=
  nonnegative_ite (p 163) (nonnegative6190 p) (nonnegative6188 p)
def d6192 (p : Pattern) : Int := if p 162 then d6191 p else d6188 p
theorem agree6192 (p q : Pattern) (h : Agree support p q) : d6192 p = d6192 q := by
  simp only [d6192, h 162 (by decide), agree6191 p q h, agree6188 p q h]
theorem nonnegative6192 (p : Pattern) : 0 ≤ d6192 p :=
  nonnegative_ite (p 162) (nonnegative6191 p) (nonnegative6188 p)
def d6193 (p : Pattern) : Int := if p 162 then d6153 p else d6191 p
theorem agree6193 (p q : Pattern) (h : Agree support p q) : d6193 p = d6193 q := by
  simp only [d6193, h 162 (by decide), agree6153 p q h, agree6191 p q h]
theorem nonnegative6193 (p : Pattern) : 0 ≤ d6193 p :=
  nonnegative_ite (p 162) (nonnegative6153 p) (nonnegative6191 p)
def d6194 (p : Pattern) : Int := if p 161 then d6193 p else d6192 p
theorem agree6194 (p q : Pattern) (h : Agree support p q) : d6194 p = d6194 q := by
  simp only [d6194, h 161 (by decide), agree6193 p q h, agree6192 p q h]
theorem nonnegative6194 (p : Pattern) : 0 ≤ d6194 p :=
  nonnegative_ite (p 161) (nonnegative6193 p) (nonnegative6192 p)
def d6195 (p : Pattern) : Int := if p 182 then d6156 p else d6169 p
theorem agree6195 (p q : Pattern) (h : Agree support p q) : d6195 p = d6195 q := by
  simp only [d6195, h 182 (by decide), agree6156 p q h, agree6169 p q h]
theorem nonnegative6195 (p : Pattern) : 0 ≤ d6195 p :=
  nonnegative_ite (p 182) (nonnegative6156 p) (nonnegative6169 p)
def d6196 (p : Pattern) : Int := if p 204 then d1903 p else d120 p
theorem agree6196 (p q : Pattern) (h : Agree support p q) : d6196 p = d6196 q := by
  simp only [d6196, h 204 (by decide), agree1903 p q h, agree120 p q h]
theorem nonnegative6196 (p : Pattern) : 0 ≤ d6196 p :=
  nonnegative_ite (p 204) (nonnegative1903 p) (nonnegative120 p)
def d6197 (p : Pattern) : Int := if p 182 then d6158 p else d6196 p
theorem agree6197 (p q : Pattern) (h : Agree support p q) : d6197 p = d6197 q := by
  simp only [d6197, h 182 (by decide), agree6158 p q h, agree6196 p q h]
theorem nonnegative6197 (p : Pattern) : 0 ≤ d6197 p :=
  nonnegative_ite (p 182) (nonnegative6158 p) (nonnegative6196 p)
def d6198 (p : Pattern) : Int := if p 163 then d6197 p else d6195 p
theorem agree6198 (p q : Pattern) (h : Agree support p q) : d6198 p = d6198 q := by
  simp only [d6198, h 163 (by decide), agree6197 p q h, agree6195 p q h]
theorem nonnegative6198 (p : Pattern) : 0 ≤ d6198 p :=
  nonnegative_ite (p 163) (nonnegative6197 p) (nonnegative6195 p)
def d6199 (p : Pattern) : Int := if p 162 then d12 p else d6198 p
theorem agree6199 (p q : Pattern) (h : Agree support p q) : d6199 p = d6199 q := by
  simp only [d6199, h 162 (by decide), agree12 p q h, agree6198 p q h]
theorem nonnegative6199 (p : Pattern) : 0 ≤ d6199 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6198 p)
def d6200 (p : Pattern) : Int := if p 161 then d12 p else d6199 p
theorem agree6200 (p q : Pattern) (h : Agree support p q) : d6200 p = d6200 q := by
  simp only [d6200, h 161 (by decide), agree12 p q h, agree6199 p q h]
theorem nonnegative6200 (p : Pattern) : 0 ≤ d6200 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6199 p)
def d6201 (p : Pattern) : Int := if p 160 then d6200 p else d6194 p
theorem agree6201 (p q : Pattern) (h : Agree support p q) : d6201 p = d6201 q := by
  simp only [d6201, h 160 (by decide), agree6200 p q h, agree6194 p q h]
theorem nonnegative6201 (p : Pattern) : 0 ≤ d6201 p :=
  nonnegative_ite (p 160) (nonnegative6200 p) (nonnegative6194 p)
def d6202 (p : Pattern) : Int := if p 163 then d6195 p else d6188 p
theorem agree6202 (p q : Pattern) (h : Agree support p q) : d6202 p = d6202 q := by
  simp only [d6202, h 163 (by decide), agree6195 p q h, agree6188 p q h]
theorem nonnegative6202 (p : Pattern) : 0 ≤ d6202 p :=
  nonnegative_ite (p 163) (nonnegative6195 p) (nonnegative6188 p)
def d6203 (p : Pattern) : Int := if p 163 then d6083 p else d6190 p
theorem agree6203 (p q : Pattern) (h : Agree support p q) : d6203 p = d6203 q := by
  simp only [d6203, h 163 (by decide), agree6083 p q h, agree6190 p q h]
theorem nonnegative6203 (p : Pattern) : 0 ≤ d6203 p :=
  nonnegative_ite (p 163) (nonnegative6083 p) (nonnegative6190 p)
def d6204 (p : Pattern) : Int := if p 162 then d6203 p else d6202 p
theorem agree6204 (p q : Pattern) (h : Agree support p q) : d6204 p = d6204 q := by
  simp only [d6204, h 162 (by decide), agree6203 p q h, agree6202 p q h]
theorem nonnegative6204 (p : Pattern) : 0 ≤ d6204 p :=
  nonnegative_ite (p 162) (nonnegative6203 p) (nonnegative6202 p)
def d6205 (p : Pattern) : Int := if p 163 then d6086 p else d6190 p
theorem agree6205 (p q : Pattern) (h : Agree support p q) : d6205 p = d6205 q := by
  simp only [d6205, h 163 (by decide), agree6086 p q h, agree6190 p q h]
theorem nonnegative6205 (p : Pattern) : 0 ≤ d6205 p :=
  nonnegative_ite (p 163) (nonnegative6086 p) (nonnegative6190 p)
def d6206 (p : Pattern) : Int := if p 162 then d12 p else d6205 p
theorem agree6206 (p q : Pattern) (h : Agree support p q) : d6206 p = d6206 q := by
  simp only [d6206, h 162 (by decide), agree12 p q h, agree6205 p q h]
theorem nonnegative6206 (p : Pattern) : 0 ≤ d6206 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6205 p)
def d6207 (p : Pattern) : Int := if p 161 then d6206 p else d6204 p
theorem agree6207 (p q : Pattern) (h : Agree support p q) : d6207 p = d6207 q := by
  simp only [d6207, h 161 (by decide), agree6206 p q h, agree6204 p q h]
theorem nonnegative6207 (p : Pattern) : 0 ≤ d6207 p :=
  nonnegative_ite (p 161) (nonnegative6206 p) (nonnegative6204 p)
def d6208 (p : Pattern) : Int := if p 163 then d12 p else d6197 p
theorem agree6208 (p q : Pattern) (h : Agree support p q) : d6208 p = d6208 q := by
  simp only [d6208, h 163 (by decide), agree12 p q h, agree6197 p q h]
theorem nonnegative6208 (p : Pattern) : 0 ≤ d6208 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6197 p)
def d6209 (p : Pattern) : Int := if p 162 then d12 p else d6208 p
theorem agree6209 (p q : Pattern) (h : Agree support p q) : d6209 p = d6209 q := by
  simp only [d6209, h 162 (by decide), agree12 p q h, agree6208 p q h]
theorem nonnegative6209 (p : Pattern) : 0 ≤ d6209 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6208 p)
def d6210 (p : Pattern) : Int := if p 161 then d12 p else d6209 p
theorem agree6210 (p q : Pattern) (h : Agree support p q) : d6210 p = d6210 q := by
  simp only [d6210, h 161 (by decide), agree12 p q h, agree6209 p q h]
theorem nonnegative6210 (p : Pattern) : 0 ≤ d6210 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6209 p)
def d6211 (p : Pattern) : Int := if p 160 then d6210 p else d6207 p
theorem agree6211 (p q : Pattern) (h : Agree support p q) : d6211 p = d6211 q := by
  simp only [d6211, h 160 (by decide), agree6210 p q h, agree6207 p q h]
theorem nonnegative6211 (p : Pattern) : 0 ≤ d6211 p :=
  nonnegative_ite (p 160) (nonnegative6210 p) (nonnegative6207 p)
def d6212 (p : Pattern) : Int := if p 141 then d6211 p else d6201 p
theorem agree6212 (p q : Pattern) (h : Agree support p q) : d6212 p = d6212 q := by
  simp only [d6212, h 141 (by decide), agree6211 p q h, agree6201 p q h]
theorem nonnegative6212 (p : Pattern) : 0 ≤ d6212 p :=
  nonnegative_ite (p 141) (nonnegative6211 p) (nonnegative6201 p)
def d6213 (p : Pattern) : Int := if p 138 then d6212 p else d6186 p
theorem agree6213 (p q : Pattern) (h : Agree support p q) : d6213 p = d6213 q := by
  simp only [d6213, h 138 (by decide), agree6212 p q h, agree6186 p q h]
theorem nonnegative6213 (p : Pattern) : 0 ≤ d6213 p :=
  nonnegative_ite (p 138) (nonnegative6212 p) (nonnegative6186 p)
def d6214 (p : Pattern) : Int := if p 162 then d12 p else d6153 p
theorem agree6214 (p q : Pattern) (h : Agree support p q) : d6214 p = d6214 q := by
  simp only [d6214, h 162 (by decide), agree12 p q h, agree6153 p q h]
theorem nonnegative6214 (p : Pattern) : 0 ≤ d6214 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6153 p)
def d6215 (p : Pattern) : Int := if p 161 then d12 p else d6214 p
theorem agree6215 (p q : Pattern) (h : Agree support p q) : d6215 p = d6215 q := by
  simp only [d6215, h 161 (by decide), agree12 p q h, agree6214 p q h]
theorem nonnegative6215 (p : Pattern) : 0 ≤ d6215 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6214 p)
def d6216 (p : Pattern) : Int := if p 160 then d12 p else d6215 p
theorem agree6216 (p q : Pattern) (h : Agree support p q) : d6216 p = d6216 q := by
  simp only [d6216, h 160 (by decide), agree12 p q h, agree6215 p q h]
theorem nonnegative6216 (p : Pattern) : 0 ≤ d6216 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative6215 p)
def d6217 (p : Pattern) : Int := if p 141 then d12 p else d6216 p
theorem agree6217 (p q : Pattern) (h : Agree support p q) : d6217 p = d6217 q := by
  simp only [d6217, h 141 (by decide), agree12 p q h, agree6216 p q h]
theorem nonnegative6217 (p : Pattern) : 0 ≤ d6217 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative6216 p)
def d6218 (p : Pattern) : Int := if p 138 then d6217 p else d6212 p
theorem agree6218 (p q : Pattern) (h : Agree support p q) : d6218 p = d6218 q := by
  simp only [d6218, h 138 (by decide), agree6217 p q h, agree6212 p q h]
theorem nonnegative6218 (p : Pattern) : 0 ≤ d6218 p :=
  nonnegative_ite (p 138) (nonnegative6217 p) (nonnegative6212 p)
def d6219 (p : Pattern) : Int := if p 116 then d6218 p else d6213 p
theorem agree6219 (p q : Pattern) (h : Agree support p q) : d6219 p = d6219 q := by
  simp only [d6219, h 116 (by decide), agree6218 p q h, agree6213 p q h]
theorem nonnegative6219 (p : Pattern) : 0 ≤ d6219 p :=
  nonnegative_ite (p 116) (nonnegative6218 p) (nonnegative6213 p)
def d6220 (p : Pattern) : Int := if p 138 then d12 p else d6212 p
theorem agree6220 (p q : Pattern) (h : Agree support p q) : d6220 p = d6220 q := by
  simp only [d6220, h 138 (by decide), agree12 p q h, agree6212 p q h]
theorem nonnegative6220 (p : Pattern) : 0 ≤ d6220 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6212 p)
def d6221 (p : Pattern) : Int := if p 116 then d6220 p else d6213 p
theorem agree6221 (p q : Pattern) (h : Agree support p q) : d6221 p = d6221 q := by
  simp only [d6221, h 116 (by decide), agree6220 p q h, agree6213 p q h]
theorem nonnegative6221 (p : Pattern) : 0 ≤ d6221 p :=
  nonnegative_ite (p 116) (nonnegative6220 p) (nonnegative6213 p)
def d6222 (p : Pattern) : Int := if p 115 then d6221 p else d6219 p
theorem agree6222 (p q : Pattern) (h : Agree support p q) : d6222 p = d6222 q := by
  simp only [d6222, h 115 (by decide), agree6221 p q h, agree6219 p q h]
theorem nonnegative6222 (p : Pattern) : 0 ≤ d6222 p :=
  nonnegative_ite (p 115) (nonnegative6221 p) (nonnegative6219 p)
def d6223 (p : Pattern) : Int := if p 71 then d6222 p else d6144 p
theorem agree6223 (p q : Pattern) (h : Agree support p q) : d6223 p = d6223 q := by
  simp only [d6223, h 71 (by decide), agree6222 p q h, agree6144 p q h]
theorem nonnegative6223 (p : Pattern) : 0 ≤ d6223 p :=
  nonnegative_ite (p 71) (nonnegative6222 p) (nonnegative6144 p)
def d6224 (p : Pattern) : Int := if p 49 then d6223 p else d6144 p
theorem agree6224 (p q : Pattern) (h : Agree support p q) : d6224 p = d6224 q := by
  simp only [d6224, h 49 (by decide), agree6223 p q h, agree6144 p q h]
theorem nonnegative6224 (p : Pattern) : 0 ≤ d6224 p :=
  nonnegative_ite (p 49) (nonnegative6223 p) (nonnegative6144 p)
def d6225 (p : Pattern) : Int := if p 182 then d6060 p else d6075 p
theorem agree6225 (p q : Pattern) (h : Agree support p q) : d6225 p = d6225 q := by
  simp only [d6225, h 182 (by decide), agree6060 p q h, agree6075 p q h]
theorem nonnegative6225 (p : Pattern) : 0 ≤ d6225 p :=
  nonnegative_ite (p 182) (nonnegative6060 p) (nonnegative6075 p)
def d6226 (p : Pattern) : Int := if p 163 then d6225 p else d6113 p
theorem agree6226 (p q : Pattern) (h : Agree support p q) : d6226 p = d6226 q := by
  simp only [d6226, h 163 (by decide), agree6225 p q h, agree6113 p q h]
theorem nonnegative6226 (p : Pattern) : 0 ≤ d6226 p :=
  nonnegative_ite (p 163) (nonnegative6225 p) (nonnegative6113 p)
def d6227 (p : Pattern) : Int := if p 182 then d6063 p else d6075 p
theorem agree6227 (p q : Pattern) (h : Agree support p q) : d6227 p = d6227 q := by
  simp only [d6227, h 182 (by decide), agree6063 p q h, agree6075 p q h]
theorem nonnegative6227 (p : Pattern) : 0 ≤ d6227 p :=
  nonnegative_ite (p 182) (nonnegative6063 p) (nonnegative6075 p)
def d6228 (p : Pattern) : Int := if p 182 then d12 p else d6114 p
theorem agree6228 (p q : Pattern) (h : Agree support p q) : d6228 p = d6228 q := by
  simp only [d6228, h 182 (by decide), agree12 p q h, agree6114 p q h]
theorem nonnegative6228 (p : Pattern) : 0 ≤ d6228 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6114 p)
def d6229 (p : Pattern) : Int := if p 163 then d6228 p else d6227 p
theorem agree6229 (p q : Pattern) (h : Agree support p q) : d6229 p = d6229 q := by
  simp only [d6229, h 163 (by decide), agree6228 p q h, agree6227 p q h]
theorem nonnegative6229 (p : Pattern) : 0 ≤ d6229 p :=
  nonnegative_ite (p 163) (nonnegative6228 p) (nonnegative6227 p)
def d6230 (p : Pattern) : Int := if p 162 then d6229 p else d6226 p
theorem agree6230 (p q : Pattern) (h : Agree support p q) : d6230 p = d6230 q := by
  simp only [d6230, h 162 (by decide), agree6229 p q h, agree6226 p q h]
theorem nonnegative6230 (p : Pattern) : 0 ≤ d6230 p :=
  nonnegative_ite (p 162) (nonnegative6229 p) (nonnegative6226 p)
def d6231 (p : Pattern) : Int := if p 163 then d6228 p else d6090 p
theorem agree6231 (p q : Pattern) (h : Agree support p q) : d6231 p = d6231 q := by
  simp only [d6231, h 163 (by decide), agree6228 p q h, agree6090 p q h]
theorem nonnegative6231 (p : Pattern) : 0 ≤ d6231 p :=
  nonnegative_ite (p 163) (nonnegative6228 p) (nonnegative6090 p)
def d6232 (p : Pattern) : Int := if p 162 then d6097 p else d6231 p
theorem agree6232 (p q : Pattern) (h : Agree support p q) : d6232 p = d6232 q := by
  simp only [d6232, h 162 (by decide), agree6097 p q h, agree6231 p q h]
theorem nonnegative6232 (p : Pattern) : 0 ≤ d6232 p :=
  nonnegative_ite (p 162) (nonnegative6097 p) (nonnegative6231 p)
def d6233 (p : Pattern) : Int := if p 161 then d6232 p else d6230 p
theorem agree6233 (p q : Pattern) (h : Agree support p q) : d6233 p = d6233 q := by
  simp only [d6233, h 161 (by decide), agree6232 p q h, agree6230 p q h]
theorem nonnegative6233 (p : Pattern) : 0 ≤ d6233 p :=
  nonnegative_ite (p 161) (nonnegative6232 p) (nonnegative6230 p)
def d6234 (p : Pattern) : Int := if p 160 then d6233 p else d6112 p
theorem agree6234 (p q : Pattern) (h : Agree support p q) : d6234 p = d6234 q := by
  simp only [d6234, h 160 (by decide), agree6233 p q h, agree6112 p q h]
theorem nonnegative6234 (p : Pattern) : 0 ≤ d6234 p :=
  nonnegative_ite (p 160) (nonnegative6233 p) (nonnegative6112 p)
def d6235 (p : Pattern) : Int := if p 163 then d6065 p else d6225 p
theorem agree6235 (p q : Pattern) (h : Agree support p q) : d6235 p = d6235 q := by
  simp only [d6235, h 163 (by decide), agree6065 p q h, agree6225 p q h]
theorem nonnegative6235 (p : Pattern) : 0 ≤ d6235 p :=
  nonnegative_ite (p 163) (nonnegative6065 p) (nonnegative6225 p)
def d6236 (p : Pattern) : Int := if p 163 then d6096 p else d6228 p
theorem agree6236 (p q : Pattern) (h : Agree support p q) : d6236 p = d6236 q := by
  simp only [d6236, h 163 (by decide), agree6096 p q h, agree6228 p q h]
theorem nonnegative6236 (p : Pattern) : 0 ≤ d6236 p :=
  nonnegative_ite (p 163) (nonnegative6096 p) (nonnegative6228 p)
def d6237 (p : Pattern) : Int := if p 162 then d6236 p else d6235 p
theorem agree6237 (p q : Pattern) (h : Agree support p q) : d6237 p = d6237 q := by
  simp only [d6237, h 162 (by decide), agree6236 p q h, agree6235 p q h]
theorem nonnegative6237 (p : Pattern) : 0 ≤ d6237 p :=
  nonnegative_ite (p 162) (nonnegative6236 p) (nonnegative6235 p)
def d6238 (p : Pattern) : Int := if p 163 then d12 p else d6228 p
theorem agree6238 (p q : Pattern) (h : Agree support p q) : d6238 p = d6238 q := by
  simp only [d6238, h 163 (by decide), agree12 p q h, agree6228 p q h]
theorem nonnegative6238 (p : Pattern) : 0 ≤ d6238 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6228 p)
def d6239 (p : Pattern) : Int := if p 162 then d12 p else d6238 p
theorem agree6239 (p q : Pattern) (h : Agree support p q) : d6239 p = d6239 q := by
  simp only [d6239, h 162 (by decide), agree12 p q h, agree6238 p q h]
theorem nonnegative6239 (p : Pattern) : 0 ≤ d6239 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6238 p)
end NetHack.Sokoban22Refined85
