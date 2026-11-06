/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5160 (p : Pattern) : Int := if p 161 then d5041 p else d5159 p
theorem agree5160 (p q : Pattern) (h : Agree support p q) : d5160 p = d5160 q := by
  simp only [d5160, h 161 (by decide), agree5041 p q h, agree5159 p q h]
theorem nonnegative5160 (p : Pattern) : 0 ≤ d5160 p :=
  nonnegative_ite (p 161) (nonnegative5041 p) (nonnegative5159 p)
def d5161 (p : Pattern) : Int := if p 163 then d12 p else d5151 p
theorem agree5161 (p q : Pattern) (h : Agree support p q) : d5161 p = d5161 q := by
  simp only [d5161, h 163 (by decide), agree12 p q h, agree5151 p q h]
theorem nonnegative5161 (p : Pattern) : 0 ≤ d5161 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5151 p)
def d5162 (p : Pattern) : Int := if p 162 then d12 p else d5161 p
theorem agree5162 (p q : Pattern) (h : Agree support p q) : d5162 p = d5162 q := by
  simp only [d5162, h 162 (by decide), agree12 p q h, agree5161 p q h]
theorem nonnegative5162 (p : Pattern) : 0 ≤ d5162 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5161 p)
def d5163 (p : Pattern) : Int := if p 161 then d12 p else d5162 p
theorem agree5163 (p q : Pattern) (h : Agree support p q) : d5163 p = d5163 q := by
  simp only [d5163, h 161 (by decide), agree12 p q h, agree5162 p q h]
theorem nonnegative5163 (p : Pattern) : 0 ≤ d5163 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5162 p)
def d5164 (p : Pattern) : Int := if p 160 then d5163 p else d5160 p
theorem agree5164 (p q : Pattern) (h : Agree support p q) : d5164 p = d5164 q := by
  simp only [d5164, h 160 (by decide), agree5163 p q h, agree5160 p q h]
theorem nonnegative5164 (p : Pattern) : 0 ≤ d5164 p :=
  nonnegative_ite (p 160) (nonnegative5163 p) (nonnegative5160 p)
def d5165 (p : Pattern) : Int := if p 141 then d5164 p else d5155 p
theorem agree5165 (p q : Pattern) (h : Agree support p q) : d5165 p = d5165 q := by
  simp only [d5165, h 141 (by decide), agree5164 p q h, agree5155 p q h]
theorem nonnegative5165 (p : Pattern) : 0 ≤ d5165 p :=
  nonnegative_ite (p 141) (nonnegative5164 p) (nonnegative5155 p)
def d5166 (p : Pattern) : Int := if p 138 then d5165 p else d5145 p
theorem agree5166 (p q : Pattern) (h : Agree support p q) : d5166 p = d5166 q := by
  simp only [d5166, h 138 (by decide), agree5165 p q h, agree5145 p q h]
theorem nonnegative5166 (p : Pattern) : 0 ≤ d5166 p :=
  nonnegative_ite (p 138) (nonnegative5165 p) (nonnegative5145 p)
def d5167 (p : Pattern) : Int := if p 138 then d12 p else d5165 p
theorem agree5167 (p q : Pattern) (h : Agree support p q) : d5167 p = d5167 q := by
  simp only [d5167, h 138 (by decide), agree12 p q h, agree5165 p q h]
theorem nonnegative5167 (p : Pattern) : 0 ≤ d5167 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5165 p)
def d5168 (p : Pattern) : Int := if p 116 then d5167 p else d5166 p
theorem agree5168 (p q : Pattern) (h : Agree support p q) : d5168 p = d5168 q := by
  simp only [d5168, h 116 (by decide), agree5167 p q h, agree5166 p q h]
theorem nonnegative5168 (p : Pattern) : 0 ≤ d5168 p :=
  nonnegative_ite (p 116) (nonnegative5167 p) (nonnegative5166 p)
def d5169 (p : Pattern) : Int := if p 115 then d5168 p else d5055 p
theorem agree5169 (p q : Pattern) (h : Agree support p q) : d5169 p = d5169 q := by
  simp only [d5169, h 115 (by decide), agree5168 p q h, agree5055 p q h]
theorem nonnegative5169 (p : Pattern) : 0 ≤ d5169 p :=
  nonnegative_ite (p 115) (nonnegative5168 p) (nonnegative5055 p)
def d5170 (p : Pattern) : Int := if p 71 then d5169 p else d5058 p
theorem agree5170 (p q : Pattern) (h : Agree support p q) : d5170 p = d5170 q := by
  simp only [d5170, h 71 (by decide), agree5169 p q h, agree5058 p q h]
theorem nonnegative5170 (p : Pattern) : 0 ≤ d5170 p :=
  nonnegative_ite (p 71) (nonnegative5169 p) (nonnegative5058 p)
def d5171 (p : Pattern) : Int := if p 163 then d12 p else d5060 p
theorem agree5171 (p q : Pattern) (h : Agree support p q) : d5171 p = d5171 q := by
  simp only [d5171, h 163 (by decide), agree12 p q h, agree5060 p q h]
theorem nonnegative5171 (p : Pattern) : 0 ≤ d5171 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5060 p)
def d5172 (p : Pattern) : Int := if p 162 then d5171 p else d5073 p
theorem agree5172 (p q : Pattern) (h : Agree support p q) : d5172 p = d5172 q := by
  simp only [d5172, h 162 (by decide), agree5171 p q h, agree5073 p q h]
theorem nonnegative5172 (p : Pattern) : 0 ≤ d5172 p :=
  nonnegative_ite (p 162) (nonnegative5171 p) (nonnegative5073 p)
def d5173 (p : Pattern) : Int := if p 162 then d12 p else d5171 p
theorem agree5173 (p q : Pattern) (h : Agree support p q) : d5173 p = d5173 q := by
  simp only [d5173, h 162 (by decide), agree12 p q h, agree5171 p q h]
theorem nonnegative5173 (p : Pattern) : 0 ≤ d5173 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5171 p)
def d5174 (p : Pattern) : Int := if p 161 then d5173 p else d5172 p
theorem agree5174 (p q : Pattern) (h : Agree support p q) : d5174 p = d5174 q := by
  simp only [d5174, h 161 (by decide), agree5173 p q h, agree5172 p q h]
theorem nonnegative5174 (p : Pattern) : 0 ≤ d5174 p :=
  nonnegative_ite (p 161) (nonnegative5173 p) (nonnegative5172 p)
def d5175 (p : Pattern) : Int := if p 162 then d215 p else d5079 p
theorem agree5175 (p q : Pattern) (h : Agree support p q) : d5175 p = d5175 q := by
  simp only [d5175, h 162 (by decide), agree215 p q h, agree5079 p q h]
theorem nonnegative5175 (p : Pattern) : 0 ≤ d5175 p :=
  nonnegative_ite (p 162) (nonnegative215 p) (nonnegative5079 p)
def d5176 (p : Pattern) : Int := if p 161 then d217 p else d5175 p
theorem agree5176 (p q : Pattern) (h : Agree support p q) : d5176 p = d5176 q := by
  simp only [d5176, h 161 (by decide), agree217 p q h, agree5175 p q h]
theorem nonnegative5176 (p : Pattern) : 0 ≤ d5176 p :=
  nonnegative_ite (p 161) (nonnegative217 p) (nonnegative5175 p)
def d5177 (p : Pattern) : Int := if p 160 then d5176 p else d5174 p
theorem agree5177 (p q : Pattern) (h : Agree support p q) : d5177 p = d5177 q := by
  simp only [d5177, h 160 (by decide), agree5176 p q h, agree5174 p q h]
theorem nonnegative5177 (p : Pattern) : 0 ≤ d5177 p :=
  nonnegative_ite (p 160) (nonnegative5176 p) (nonnegative5174 p)
def d5178 (p : Pattern) : Int := if p 141 then d5177 p else d5071 p
theorem agree5178 (p q : Pattern) (h : Agree support p q) : d5178 p = d5178 q := by
  simp only [d5178, h 141 (by decide), agree5177 p q h, agree5071 p q h]
theorem nonnegative5178 (p : Pattern) : 0 ≤ d5178 p :=
  nonnegative_ite (p 141) (nonnegative5177 p) (nonnegative5071 p)
def d5179 (p : Pattern) : Int := if p 163 then d12 p else d5088 p
theorem agree5179 (p q : Pattern) (h : Agree support p q) : d5179 p = d5179 q := by
  simp only [d5179, h 163 (by decide), agree12 p q h, agree5088 p q h]
theorem nonnegative5179 (p : Pattern) : 0 ≤ d5179 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5088 p)
def d5180 (p : Pattern) : Int := if p 162 then d5179 p else d5099 p
theorem agree5180 (p q : Pattern) (h : Agree support p q) : d5180 p = d5180 q := by
  simp only [d5180, h 162 (by decide), agree5179 p q h, agree5099 p q h]
theorem nonnegative5180 (p : Pattern) : 0 ≤ d5180 p :=
  nonnegative_ite (p 162) (nonnegative5179 p) (nonnegative5099 p)
def d5181 (p : Pattern) : Int := if p 162 then d12 p else d5179 p
theorem agree5181 (p q : Pattern) (h : Agree support p q) : d5181 p = d5181 q := by
  simp only [d5181, h 162 (by decide), agree12 p q h, agree5179 p q h]
theorem nonnegative5181 (p : Pattern) : 0 ≤ d5181 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5179 p)
def d5182 (p : Pattern) : Int := if p 161 then d5181 p else d5180 p
theorem agree5182 (p q : Pattern) (h : Agree support p q) : d5182 p = d5182 q := by
  simp only [d5182, h 161 (by decide), agree5181 p q h, agree5180 p q h]
theorem nonnegative5182 (p : Pattern) : 0 ≤ d5182 p :=
  nonnegative_ite (p 161) (nonnegative5181 p) (nonnegative5180 p)
def d5183 (p : Pattern) : Int := if p 160 then d5107 p else d5182 p
theorem agree5183 (p q : Pattern) (h : Agree support p q) : d5183 p = d5183 q := by
  simp only [d5183, h 160 (by decide), agree5107 p q h, agree5182 p q h]
theorem nonnegative5183 (p : Pattern) : 0 ≤ d5183 p :=
  nonnegative_ite (p 160) (nonnegative5107 p) (nonnegative5182 p)
def d5184 (p : Pattern) : Int := if p 141 then d5183 p else d5098 p
theorem agree5184 (p q : Pattern) (h : Agree support p q) : d5184 p = d5184 q := by
  simp only [d5184, h 141 (by decide), agree5183 p q h, agree5098 p q h]
theorem nonnegative5184 (p : Pattern) : 0 ≤ d5184 p :=
  nonnegative_ite (p 141) (nonnegative5183 p) (nonnegative5098 p)
def d5185 (p : Pattern) : Int := if p 138 then d5184 p else d5178 p
theorem agree5185 (p q : Pattern) (h : Agree support p q) : d5185 p = d5185 q := by
  simp only [d5185, h 138 (by decide), agree5184 p q h, agree5178 p q h]
theorem nonnegative5185 (p : Pattern) : 0 ≤ d5185 p :=
  nonnegative_ite (p 138) (nonnegative5184 p) (nonnegative5178 p)
def d5186 (p : Pattern) : Int := if p 138 then d5114 p else d5184 p
theorem agree5186 (p q : Pattern) (h : Agree support p q) : d5186 p = d5186 q := by
  simp only [d5186, h 138 (by decide), agree5114 p q h, agree5184 p q h]
theorem nonnegative5186 (p : Pattern) : 0 ≤ d5186 p :=
  nonnegative_ite (p 138) (nonnegative5114 p) (nonnegative5184 p)
def d5187 (p : Pattern) : Int := if p 116 then d5186 p else d5185 p
theorem agree5187 (p q : Pattern) (h : Agree support p q) : d5187 p = d5187 q := by
  simp only [d5187, h 116 (by decide), agree5186 p q h, agree5185 p q h]
theorem nonnegative5187 (p : Pattern) : 0 ≤ d5187 p :=
  nonnegative_ite (p 116) (nonnegative5186 p) (nonnegative5185 p)
def d5188 (p : Pattern) : Int := if p 182 then d2108 p else d103 p
theorem agree5188 (p q : Pattern) (h : Agree support p q) : d5188 p = d5188 q := by
  simp only [d5188, h 182 (by decide), agree2108 p q h, agree103 p q h]
theorem nonnegative5188 (p : Pattern) : 0 ≤ d5188 p :=
  nonnegative_ite (p 182) (nonnegative2108 p) (nonnegative103 p)
def d5189 (p : Pattern) : Int := if p 163 then d5088 p else d5188 p
theorem agree5189 (p q : Pattern) (h : Agree support p q) : d5189 p = d5189 q := by
  simp only [d5189, h 163 (by decide), agree5088 p q h, agree5188 p q h]
theorem nonnegative5189 (p : Pattern) : 0 ≤ d5189 p :=
  nonnegative_ite (p 163) (nonnegative5088 p) (nonnegative5188 p)
def d5190 (p : Pattern) : Int := if p 162 then d5189 p else d5084 p
theorem agree5190 (p q : Pattern) (h : Agree support p q) : d5190 p = d5190 q := by
  simp only [d5190, h 162 (by decide), agree5189 p q h, agree5084 p q h]
theorem nonnegative5190 (p : Pattern) : 0 ≤ d5190 p :=
  nonnegative_ite (p 162) (nonnegative5189 p) (nonnegative5084 p)
def d5191 (p : Pattern) : Int := if p 163 then d5088 p else d5085 p
theorem agree5191 (p q : Pattern) (h : Agree support p q) : d5191 p = d5191 q := by
  simp only [d5191, h 163 (by decide), agree5088 p q h, agree5085 p q h]
theorem nonnegative5191 (p : Pattern) : 0 ≤ d5191 p :=
  nonnegative_ite (p 163) (nonnegative5088 p) (nonnegative5085 p)
def d5192 (p : Pattern) : Int := if p 162 then d5063 p else d5191 p
theorem agree5192 (p q : Pattern) (h : Agree support p q) : d5192 p = d5192 q := by
  simp only [d5192, h 162 (by decide), agree5063 p q h, agree5191 p q h]
theorem nonnegative5192 (p : Pattern) : 0 ≤ d5192 p :=
  nonnegative_ite (p 162) (nonnegative5063 p) (nonnegative5191 p)
def d5193 (p : Pattern) : Int := if p 161 then d5192 p else d5190 p
theorem agree5193 (p q : Pattern) (h : Agree support p q) : d5193 p = d5193 q := by
  simp only [d5193, h 161 (by decide), agree5192 p q h, agree5190 p q h]
theorem nonnegative5193 (p : Pattern) : 0 ≤ d5193 p :=
  nonnegative_ite (p 161) (nonnegative5192 p) (nonnegative5190 p)
def d5194 (p : Pattern) : Int := if p 182 then d1905 p else d116 p
theorem agree5194 (p q : Pattern) (h : Agree support p q) : d5194 p = d5194 q := by
  simp only [d5194, h 182 (by decide), agree1905 p q h, agree116 p q h]
theorem nonnegative5194 (p : Pattern) : 0 ≤ d5194 p :=
  nonnegative_ite (p 182) (nonnegative1905 p) (nonnegative116 p)
def d5195 (p : Pattern) : Int := if p 163 then d5194 p else d5093 p
theorem agree5195 (p q : Pattern) (h : Agree support p q) : d5195 p = d5195 q := by
  simp only [d5195, h 163 (by decide), agree5194 p q h, agree5093 p q h]
theorem nonnegative5195 (p : Pattern) : 0 ≤ d5195 p :=
  nonnegative_ite (p 163) (nonnegative5194 p) (nonnegative5093 p)
def d5196 (p : Pattern) : Int := if p 162 then d215 p else d5195 p
theorem agree5196 (p q : Pattern) (h : Agree support p q) : d5196 p = d5196 q := by
  simp only [d5196, h 162 (by decide), agree215 p q h, agree5195 p q h]
theorem nonnegative5196 (p : Pattern) : 0 ≤ d5196 p :=
  nonnegative_ite (p 162) (nonnegative215 p) (nonnegative5195 p)
def d5197 (p : Pattern) : Int := if p 161 then d231 p else d5196 p
theorem agree5197 (p q : Pattern) (h : Agree support p q) : d5197 p = d5197 q := by
  simp only [d5197, h 161 (by decide), agree231 p q h, agree5196 p q h]
theorem nonnegative5197 (p : Pattern) : 0 ≤ d5197 p :=
  nonnegative_ite (p 161) (nonnegative231 p) (nonnegative5196 p)
def d5198 (p : Pattern) : Int := if p 160 then d5197 p else d5193 p
theorem agree5198 (p q : Pattern) (h : Agree support p q) : d5198 p = d5198 q := by
  simp only [d5198, h 160 (by decide), agree5197 p q h, agree5193 p q h]
theorem nonnegative5198 (p : Pattern) : 0 ≤ d5198 p :=
  nonnegative_ite (p 160) (nonnegative5197 p) (nonnegative5193 p)
def d5199 (p : Pattern) : Int := if p 182 then d2125 p else d116 p
theorem agree5199 (p q : Pattern) (h : Agree support p q) : d5199 p = d5199 q := by
  simp only [d5199, h 182 (by decide), agree2125 p q h, agree116 p q h]
theorem nonnegative5199 (p : Pattern) : 0 ≤ d5199 p :=
  nonnegative_ite (p 182) (nonnegative2125 p) (nonnegative116 p)
def d5200 (p : Pattern) : Int := if p 163 then d5199 p else d5188 p
theorem agree5200 (p q : Pattern) (h : Agree support p q) : d5200 p = d5200 q := by
  simp only [d5200, h 163 (by decide), agree5199 p q h, agree5188 p q h]
theorem nonnegative5200 (p : Pattern) : 0 ≤ d5200 p :=
  nonnegative_ite (p 163) (nonnegative5199 p) (nonnegative5188 p)
def d5201 (p : Pattern) : Int := if p 182 then d2130 p else d107 p
theorem agree5201 (p q : Pattern) (h : Agree support p q) : d5201 p = d5201 q := by
  simp only [d5201, h 182 (by decide), agree2130 p q h, agree107 p q h]
theorem nonnegative5201 (p : Pattern) : 0 ≤ d5201 p :=
  nonnegative_ite (p 182) (nonnegative2130 p) (nonnegative107 p)
def d5202 (p : Pattern) : Int := if p 163 then d12 p else d5201 p
theorem agree5202 (p q : Pattern) (h : Agree support p q) : d5202 p = d5202 q := by
  simp only [d5202, h 163 (by decide), agree12 p q h, agree5201 p q h]
theorem nonnegative5202 (p : Pattern) : 0 ≤ d5202 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5201 p)
def d5203 (p : Pattern) : Int := if p 162 then d5202 p else d5200 p
theorem agree5203 (p q : Pattern) (h : Agree support p q) : d5203 p = d5203 q := by
  simp only [d5203, h 162 (by decide), agree5202 p q h, agree5200 p q h]
theorem nonnegative5203 (p : Pattern) : 0 ≤ d5203 p :=
  nonnegative_ite (p 162) (nonnegative5202 p) (nonnegative5200 p)
def d5204 (p : Pattern) : Int := if p 182 then d2136 p else d107 p
theorem agree5204 (p q : Pattern) (h : Agree support p q) : d5204 p = d5204 q := by
  simp only [d5204, h 182 (by decide), agree2136 p q h, agree107 p q h]
theorem nonnegative5204 (p : Pattern) : 0 ≤ d5204 p :=
  nonnegative_ite (p 182) (nonnegative2136 p) (nonnegative107 p)
def d5205 (p : Pattern) : Int := if p 163 then d12 p else d5204 p
theorem agree5205 (p q : Pattern) (h : Agree support p q) : d5205 p = d5205 q := by
  simp only [d5205, h 163 (by decide), agree12 p q h, agree5204 p q h]
theorem nonnegative5205 (p : Pattern) : 0 ≤ d5205 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5204 p)
def d5206 (p : Pattern) : Int := if p 162 then d12 p else d5205 p
theorem agree5206 (p q : Pattern) (h : Agree support p q) : d5206 p = d5206 q := by
  simp only [d5206, h 162 (by decide), agree12 p q h, agree5205 p q h]
theorem nonnegative5206 (p : Pattern) : 0 ≤ d5206 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5205 p)
def d5207 (p : Pattern) : Int := if p 161 then d5206 p else d5203 p
theorem agree5207 (p q : Pattern) (h : Agree support p q) : d5207 p = d5207 q := by
  simp only [d5207, h 161 (by decide), agree5206 p q h, agree5203 p q h]
theorem nonnegative5207 (p : Pattern) : 0 ≤ d5207 p :=
  nonnegative_ite (p 161) (nonnegative5206 p) (nonnegative5203 p)
def d5208 (p : Pattern) : Int := if p 182 then d1905 p else d107 p
theorem agree5208 (p q : Pattern) (h : Agree support p q) : d5208 p = d5208 q := by
  simp only [d5208, h 182 (by decide), agree1905 p q h, agree107 p q h]
theorem nonnegative5208 (p : Pattern) : 0 ≤ d5208 p :=
  nonnegative_ite (p 182) (nonnegative1905 p) (nonnegative107 p)
def d5209 (p : Pattern) : Int := if p 163 then d125 p else d5208 p
theorem agree5209 (p q : Pattern) (h : Agree support p q) : d5209 p = d5209 q := by
  simp only [d5209, h 163 (by decide), agree125 p q h, agree5208 p q h]
theorem nonnegative5209 (p : Pattern) : 0 ≤ d5209 p :=
  nonnegative_ite (p 163) (nonnegative125 p) (nonnegative5208 p)
def d5210 (p : Pattern) : Int := if p 162 then d230 p else d5209 p
theorem agree5210 (p q : Pattern) (h : Agree support p q) : d5210 p = d5210 q := by
  simp only [d5210, h 162 (by decide), agree230 p q h, agree5209 p q h]
theorem nonnegative5210 (p : Pattern) : 0 ≤ d5210 p :=
  nonnegative_ite (p 162) (nonnegative230 p) (nonnegative5209 p)
def d5211 (p : Pattern) : Int := if p 161 then d237 p else d5210 p
theorem agree5211 (p q : Pattern) (h : Agree support p q) : d5211 p = d5211 q := by
  simp only [d5211, h 161 (by decide), agree237 p q h, agree5210 p q h]
theorem nonnegative5211 (p : Pattern) : 0 ≤ d5211 p :=
  nonnegative_ite (p 161) (nonnegative237 p) (nonnegative5210 p)
def d5212 (p : Pattern) : Int := if p 160 then d5211 p else d5207 p
theorem agree5212 (p q : Pattern) (h : Agree support p q) : d5212 p = d5212 q := by
  simp only [d5212, h 160 (by decide), agree5211 p q h, agree5207 p q h]
theorem nonnegative5212 (p : Pattern) : 0 ≤ d5212 p :=
  nonnegative_ite (p 160) (nonnegative5211 p) (nonnegative5207 p)
def d5213 (p : Pattern) : Int := if p 141 then d5212 p else d5198 p
theorem agree5213 (p q : Pattern) (h : Agree support p q) : d5213 p = d5213 q := by
  simp only [d5213, h 141 (by decide), agree5212 p q h, agree5198 p q h]
theorem nonnegative5213 (p : Pattern) : 0 ≤ d5213 p :=
  nonnegative_ite (p 141) (nonnegative5212 p) (nonnegative5198 p)
def d5214 (p : Pattern) : Int := if p 163 then d5087 p else d5085 p
theorem agree5214 (p q : Pattern) (h : Agree support p q) : d5214 p = d5214 q := by
  simp only [d5214, h 163 (by decide), agree5087 p q h, agree5085 p q h]
theorem nonnegative5214 (p : Pattern) : 0 ≤ d5214 p :=
  nonnegative_ite (p 163) (nonnegative5087 p) (nonnegative5085 p)
def d5215 (p : Pattern) : Int := if p 163 then d5008 p else d5093 p
theorem agree5215 (p q : Pattern) (h : Agree support p q) : d5215 p = d5215 q := by
  simp only [d5215, h 163 (by decide), agree5008 p q h, agree5093 p q h]
theorem nonnegative5215 (p : Pattern) : 0 ≤ d5215 p :=
  nonnegative_ite (p 163) (nonnegative5008 p) (nonnegative5093 p)
def d5216 (p : Pattern) : Int := if p 162 then d5215 p else d5214 p
theorem agree5216 (p q : Pattern) (h : Agree support p q) : d5216 p = d5216 q := by
  simp only [d5216, h 162 (by decide), agree5215 p q h, agree5214 p q h]
theorem nonnegative5216 (p : Pattern) : 0 ≤ d5216 p :=
  nonnegative_ite (p 162) (nonnegative5215 p) (nonnegative5214 p)
def d5217 (p : Pattern) : Int := if p 161 then d5103 p else d5216 p
theorem agree5217 (p q : Pattern) (h : Agree support p q) : d5217 p = d5217 q := by
  simp only [d5217, h 161 (by decide), agree5103 p q h, agree5216 p q h]
theorem nonnegative5217 (p : Pattern) : 0 ≤ d5217 p :=
  nonnegative_ite (p 161) (nonnegative5103 p) (nonnegative5216 p)
def d5218 (p : Pattern) : Int := if p 160 then d5107 p else d5217 p
theorem agree5218 (p q : Pattern) (h : Agree support p q) : d5218 p = d5218 q := by
  simp only [d5218, h 160 (by decide), agree5107 p q h, agree5217 p q h]
theorem nonnegative5218 (p : Pattern) : 0 ≤ d5218 p :=
  nonnegative_ite (p 160) (nonnegative5107 p) (nonnegative5217 p)
def d5219 (p : Pattern) : Int := if p 182 then d2157 p else d116 p
theorem agree5219 (p q : Pattern) (h : Agree support p q) : d5219 p = d5219 q := by
  simp only [d5219, h 182 (by decide), agree2157 p q h, agree116 p q h]
theorem nonnegative5219 (p : Pattern) : 0 ≤ d5219 p :=
  nonnegative_ite (p 182) (nonnegative2157 p) (nonnegative116 p)
def d5220 (p : Pattern) : Int := if p 163 then d5093 p else d5219 p
theorem agree5220 (p q : Pattern) (h : Agree support p q) : d5220 p = d5220 q := by
  simp only [d5220, h 163 (by decide), agree5093 p q h, agree5219 p q h]
theorem nonnegative5220 (p : Pattern) : 0 ≤ d5220 p :=
  nonnegative_ite (p 163) (nonnegative5093 p) (nonnegative5219 p)
def d5221 (p : Pattern) : Int := if p 162 then d5179 p else d5220 p
theorem agree5221 (p q : Pattern) (h : Agree support p q) : d5221 p = d5221 q := by
  simp only [d5221, h 162 (by decide), agree5179 p q h, agree5220 p q h]
theorem nonnegative5221 (p : Pattern) : 0 ≤ d5221 p :=
  nonnegative_ite (p 162) (nonnegative5179 p) (nonnegative5220 p)
def d5222 (p : Pattern) : Int := if p 161 then d5106 p else d5221 p
theorem agree5222 (p q : Pattern) (h : Agree support p q) : d5222 p = d5222 q := by
  simp only [d5222, h 161 (by decide), agree5106 p q h, agree5221 p q h]
theorem nonnegative5222 (p : Pattern) : 0 ≤ d5222 p :=
  nonnegative_ite (p 161) (nonnegative5106 p) (nonnegative5221 p)
def d5223 (p : Pattern) : Int := if p 162 then d12 p else d5025 p
theorem agree5223 (p q : Pattern) (h : Agree support p q) : d5223 p = d5223 q := by
  simp only [d5223, h 162 (by decide), agree12 p q h, agree5025 p q h]
theorem nonnegative5223 (p : Pattern) : 0 ≤ d5223 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5025 p)
def d5224 (p : Pattern) : Int := if p 161 then d12 p else d5223 p
theorem agree5224 (p q : Pattern) (h : Agree support p q) : d5224 p = d5224 q := by
  simp only [d5224, h 161 (by decide), agree12 p q h, agree5223 p q h]
theorem nonnegative5224 (p : Pattern) : 0 ≤ d5224 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5223 p)
def d5225 (p : Pattern) : Int := if p 160 then d5224 p else d5222 p
theorem agree5225 (p q : Pattern) (h : Agree support p q) : d5225 p = d5225 q := by
  simp only [d5225, h 160 (by decide), agree5224 p q h, agree5222 p q h]
theorem nonnegative5225 (p : Pattern) : 0 ≤ d5225 p :=
  nonnegative_ite (p 160) (nonnegative5224 p) (nonnegative5222 p)
def d5226 (p : Pattern) : Int := if p 141 then d5225 p else d5218 p
theorem agree5226 (p q : Pattern) (h : Agree support p q) : d5226 p = d5226 q := by
  simp only [d5226, h 141 (by decide), agree5225 p q h, agree5218 p q h]
theorem nonnegative5226 (p : Pattern) : 0 ≤ d5226 p :=
  nonnegative_ite (p 141) (nonnegative5225 p) (nonnegative5218 p)
def d5227 (p : Pattern) : Int := if p 138 then d5226 p else d5213 p
theorem agree5227 (p q : Pattern) (h : Agree support p q) : d5227 p = d5227 q := by
  simp only [d5227, h 138 (by decide), agree5226 p q h, agree5213 p q h]
theorem nonnegative5227 (p : Pattern) : 0 ≤ d5227 p :=
  nonnegative_ite (p 138) (nonnegative5226 p) (nonnegative5213 p)
def d5228 (p : Pattern) : Int := if p 163 then d5024 p else d5093 p
theorem agree5228 (p q : Pattern) (h : Agree support p q) : d5228 p = d5228 q := by
  simp only [d5228, h 163 (by decide), agree5024 p q h, agree5093 p q h]
theorem nonnegative5228 (p : Pattern) : 0 ≤ d5228 p :=
  nonnegative_ite (p 163) (nonnegative5024 p) (nonnegative5093 p)
def d5229 (p : Pattern) : Int := if p 162 then d5228 p else d5214 p
theorem agree5229 (p q : Pattern) (h : Agree support p q) : d5229 p = d5229 q := by
  simp only [d5229, h 162 (by decide), agree5228 p q h, agree5214 p q h]
theorem nonnegative5229 (p : Pattern) : 0 ≤ d5229 p :=
  nonnegative_ite (p 162) (nonnegative5228 p) (nonnegative5214 p)
def d5230 (p : Pattern) : Int := if p 163 then d5024 p else d5088 p
theorem agree5230 (p q : Pattern) (h : Agree support p q) : d5230 p = d5230 q := by
  simp only [d5230, h 163 (by decide), agree5024 p q h, agree5088 p q h]
theorem nonnegative5230 (p : Pattern) : 0 ≤ d5230 p :=
  nonnegative_ite (p 163) (nonnegative5024 p) (nonnegative5088 p)
def d5231 (p : Pattern) : Int := if p 162 then d12 p else d5230 p
theorem agree5231 (p q : Pattern) (h : Agree support p q) : d5231 p = d5231 q := by
  simp only [d5231, h 162 (by decide), agree12 p q h, agree5230 p q h]
theorem nonnegative5231 (p : Pattern) : 0 ≤ d5231 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5230 p)
def d5232 (p : Pattern) : Int := if p 161 then d5231 p else d5229 p
theorem agree5232 (p q : Pattern) (h : Agree support p q) : d5232 p = d5232 q := by
  simp only [d5232, h 161 (by decide), agree5231 p q h, agree5229 p q h]
theorem nonnegative5232 (p : Pattern) : 0 ≤ d5232 p :=
  nonnegative_ite (p 161) (nonnegative5231 p) (nonnegative5229 p)
def d5233 (p : Pattern) : Int := if p 163 then d5008 p else d5094 p
theorem agree5233 (p q : Pattern) (h : Agree support p q) : d5233 p = d5233 q := by
  simp only [d5233, h 163 (by decide), agree5008 p q h, agree5094 p q h]
theorem nonnegative5233 (p : Pattern) : 0 ≤ d5233 p :=
  nonnegative_ite (p 163) (nonnegative5008 p) (nonnegative5094 p)
def d5234 (p : Pattern) : Int := if p 162 then d12 p else d5233 p
theorem agree5234 (p q : Pattern) (h : Agree support p q) : d5234 p = d5234 q := by
  simp only [d5234, h 162 (by decide), agree12 p q h, agree5233 p q h]
theorem nonnegative5234 (p : Pattern) : 0 ≤ d5234 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5233 p)
def d5235 (p : Pattern) : Int := if p 161 then d12 p else d5234 p
theorem agree5235 (p q : Pattern) (h : Agree support p q) : d5235 p = d5235 q := by
  simp only [d5235, h 161 (by decide), agree12 p q h, agree5234 p q h]
theorem nonnegative5235 (p : Pattern) : 0 ≤ d5235 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5234 p)
def d5236 (p : Pattern) : Int := if p 160 then d5235 p else d5232 p
theorem agree5236 (p q : Pattern) (h : Agree support p q) : d5236 p = d5236 q := by
  simp only [d5236, h 160 (by decide), agree5235 p q h, agree5232 p q h]
theorem nonnegative5236 (p : Pattern) : 0 ≤ d5236 p :=
  nonnegative_ite (p 160) (nonnegative5235 p) (nonnegative5232 p)
def d5237 (p : Pattern) : Int := if p 141 then d5225 p else d5236 p
theorem agree5237 (p q : Pattern) (h : Agree support p q) : d5237 p = d5237 q := by
  simp only [d5237, h 141 (by decide), agree5225 p q h, agree5236 p q h]
theorem nonnegative5237 (p : Pattern) : 0 ≤ d5237 p :=
  nonnegative_ite (p 141) (nonnegative5225 p) (nonnegative5236 p)
def d5238 (p : Pattern) : Int := if p 138 then d12 p else d5237 p
theorem agree5238 (p q : Pattern) (h : Agree support p q) : d5238 p = d5238 q := by
  simp only [d5238, h 138 (by decide), agree12 p q h, agree5237 p q h]
theorem nonnegative5238 (p : Pattern) : 0 ≤ d5238 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5237 p)
def d5239 (p : Pattern) : Int := if p 116 then d5238 p else d5227 p
theorem agree5239 (p q : Pattern) (h : Agree support p q) : d5239 p = d5239 q := by
  simp only [d5239, h 116 (by decide), agree5238 p q h, agree5227 p q h]
theorem nonnegative5239 (p : Pattern) : 0 ≤ d5239 p :=
  nonnegative_ite (p 116) (nonnegative5238 p) (nonnegative5227 p)
def d5240 (p : Pattern) : Int := if p 115 then d5239 p else d5187 p
theorem agree5240 (p q : Pattern) (h : Agree support p q) : d5240 p = d5240 q := by
  simp only [d5240, h 115 (by decide), agree5239 p q h, agree5187 p q h]
theorem nonnegative5240 (p : Pattern) : 0 ≤ d5240 p :=
  nonnegative_ite (p 115) (nonnegative5239 p) (nonnegative5187 p)
def d5241 (p : Pattern) : Int := if p 71 then d5240 p else d5058 p
theorem agree5241 (p q : Pattern) (h : Agree support p q) : d5241 p = d5241 q := by
  simp only [d5241, h 71 (by decide), agree5240 p q h, agree5058 p q h]
theorem nonnegative5241 (p : Pattern) : 0 ≤ d5241 p :=
  nonnegative_ite (p 71) (nonnegative5240 p) (nonnegative5058 p)
def d5242 (p : Pattern) : Int := if p 49 then d5241 p else d5170 p
theorem agree5242 (p q : Pattern) (h : Agree support p q) : d5242 p = d5242 q := by
  simp only [d5242, h 49 (by decide), agree5241 p q h, agree5170 p q h]
theorem nonnegative5242 (p : Pattern) : 0 ≤ d5242 p :=
  nonnegative_ite (p 49) (nonnegative5241 p) (nonnegative5170 p)
def d5243 (p : Pattern) : Int := if p 48 then d5242 p else d5121 p
theorem agree5243 (p q : Pattern) (h : Agree support p q) : d5243 p = d5243 q := by
  simp only [d5243, h 48 (by decide), agree5242 p q h, agree5121 p q h]
theorem nonnegative5243 (p : Pattern) : 0 ≤ d5243 p :=
  nonnegative_ite (p 48) (nonnegative5242 p) (nonnegative5121 p)
def d5244 (p : Pattern) : Int := if p 138 then d4321 p else d4317 p
theorem agree5244 (p q : Pattern) (h : Agree support p q) : d5244 p = d5244 q := by
  simp only [d5244, h 138 (by decide), agree4321 p q h, agree4317 p q h]
theorem nonnegative5244 (p : Pattern) : 0 ≤ d5244 p :=
  nonnegative_ite (p 138) (nonnegative4321 p) (nonnegative4317 p)
def d5245 (p : Pattern) : Int := if p 138 then d4162 p else d4321 p
theorem agree5245 (p q : Pattern) (h : Agree support p q) : d5245 p = d5245 q := by
  simp only [d5245, h 138 (by decide), agree4162 p q h, agree4321 p q h]
theorem nonnegative5245 (p : Pattern) : 0 ≤ d5245 p :=
  nonnegative_ite (p 138) (nonnegative4162 p) (nonnegative4321 p)
def d5246 (p : Pattern) : Int := if p 116 then d5245 p else d5244 p
theorem agree5246 (p q : Pattern) (h : Agree support p q) : d5246 p = d5246 q := by
  simp only [d5246, h 116 (by decide), agree5245 p q h, agree5244 p q h]
theorem nonnegative5246 (p : Pattern) : 0 ≤ d5246 p :=
  nonnegative_ite (p 116) (nonnegative5245 p) (nonnegative5244 p)
def d5247 (p : Pattern) : Int := if p 138 then d12 p else d4321 p
theorem agree5247 (p q : Pattern) (h : Agree support p q) : d5247 p = d5247 q := by
  simp only [d5247, h 138 (by decide), agree12 p q h, agree4321 p q h]
theorem nonnegative5247 (p : Pattern) : 0 ≤ d5247 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4321 p)
def d5248 (p : Pattern) : Int := if p 116 then d5247 p else d5244 p
theorem agree5248 (p q : Pattern) (h : Agree support p q) : d5248 p = d5248 q := by
  simp only [d5248, h 116 (by decide), agree5247 p q h, agree5244 p q h]
theorem nonnegative5248 (p : Pattern) : 0 ≤ d5248 p :=
  nonnegative_ite (p 116) (nonnegative5247 p) (nonnegative5244 p)
def d5249 (p : Pattern) : Int := if p 115 then d5248 p else d5246 p
theorem agree5249 (p q : Pattern) (h : Agree support p q) : d5249 p = d5249 q := by
  simp only [d5249, h 115 (by decide), agree5248 p q h, agree5246 p q h]
theorem nonnegative5249 (p : Pattern) : 0 ≤ d5249 p :=
  nonnegative_ite (p 115) (nonnegative5248 p) (nonnegative5246 p)
def d5250 (p : Pattern) : Int := if p 138 then d4347 p else d4344 p
theorem agree5250 (p q : Pattern) (h : Agree support p q) : d5250 p = d5250 q := by
  simp only [d5250, h 138 (by decide), agree4347 p q h, agree4344 p q h]
theorem nonnegative5250 (p : Pattern) : 0 ≤ d5250 p :=
  nonnegative_ite (p 138) (nonnegative4347 p) (nonnegative4344 p)
def d5251 (p : Pattern) : Int := if p 138 then d12 p else d4347 p
theorem agree5251 (p q : Pattern) (h : Agree support p q) : d5251 p = d5251 q := by
  simp only [d5251, h 138 (by decide), agree12 p q h, agree4347 p q h]
theorem nonnegative5251 (p : Pattern) : 0 ≤ d5251 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4347 p)
def d5252 (p : Pattern) : Int := if p 116 then d5251 p else d5250 p
theorem agree5252 (p q : Pattern) (h : Agree support p q) : d5252 p = d5252 q := by
  simp only [d5252, h 116 (by decide), agree5251 p q h, agree5250 p q h]
theorem nonnegative5252 (p : Pattern) : 0 ≤ d5252 p :=
  nonnegative_ite (p 116) (nonnegative5251 p) (nonnegative5250 p)
def d5253 (p : Pattern) : Int := if p 71 then d5252 p else d5249 p
theorem agree5253 (p q : Pattern) (h : Agree support p q) : d5253 p = d5253 q := by
  simp only [d5253, h 71 (by decide), agree5252 p q h, agree5249 p q h]
theorem nonnegative5253 (p : Pattern) : 0 ≤ d5253 p :=
  nonnegative_ite (p 71) (nonnegative5252 p) (nonnegative5249 p)
def d5254 (p : Pattern) : Int := if p 49 then d5253 p else d5249 p
theorem agree5254 (p q : Pattern) (h : Agree support p q) : d5254 p = d5254 q := by
  simp only [d5254, h 49 (by decide), agree5253 p q h, agree5249 p q h]
theorem nonnegative5254 (p : Pattern) : 0 ≤ d5254 p :=
  nonnegative_ite (p 49) (nonnegative5253 p) (nonnegative5249 p)
def d5255 (p : Pattern) : Int := if p 138 then d4362 p else d4317 p
theorem agree5255 (p q : Pattern) (h : Agree support p q) : d5255 p = d5255 q := by
  simp only [d5255, h 138 (by decide), agree4362 p q h, agree4317 p q h]
theorem nonnegative5255 (p : Pattern) : 0 ≤ d5255 p :=
  nonnegative_ite (p 138) (nonnegative4362 p) (nonnegative4317 p)
def d5256 (p : Pattern) : Int := if p 138 then d12 p else d4362 p
theorem agree5256 (p q : Pattern) (h : Agree support p q) : d5256 p = d5256 q := by
  simp only [d5256, h 138 (by decide), agree12 p q h, agree4362 p q h]
theorem nonnegative5256 (p : Pattern) : 0 ≤ d5256 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4362 p)
def d5257 (p : Pattern) : Int := if p 116 then d5256 p else d5255 p
theorem agree5257 (p q : Pattern) (h : Agree support p q) : d5257 p = d5257 q := by
  simp only [d5257, h 116 (by decide), agree5256 p q h, agree5255 p q h]
theorem nonnegative5257 (p : Pattern) : 0 ≤ d5257 p :=
  nonnegative_ite (p 116) (nonnegative5256 p) (nonnegative5255 p)
def d5258 (p : Pattern) : Int := if p 115 then d5257 p else d5246 p
theorem agree5258 (p q : Pattern) (h : Agree support p q) : d5258 p = d5258 q := by
  simp only [d5258, h 115 (by decide), agree5257 p q h, agree5246 p q h]
theorem nonnegative5258 (p : Pattern) : 0 ≤ d5258 p :=
  nonnegative_ite (p 115) (nonnegative5257 p) (nonnegative5246 p)
def d5259 (p : Pattern) : Int := if p 71 then d5258 p else d5249 p
theorem agree5259 (p q : Pattern) (h : Agree support p q) : d5259 p = d5259 q := by
  simp only [d5259, h 71 (by decide), agree5258 p q h, agree5249 p q h]
theorem nonnegative5259 (p : Pattern) : 0 ≤ d5259 p :=
  nonnegative_ite (p 71) (nonnegative5258 p) (nonnegative5249 p)
def d5260 (p : Pattern) : Int := if p 138 then d4385 p else d4376 p
theorem agree5260 (p q : Pattern) (h : Agree support p q) : d5260 p = d5260 q := by
  simp only [d5260, h 138 (by decide), agree4385 p q h, agree4376 p q h]
theorem nonnegative5260 (p : Pattern) : 0 ≤ d5260 p :=
  nonnegative_ite (p 138) (nonnegative4385 p) (nonnegative4376 p)
def d5261 (p : Pattern) : Int := if p 138 then d12 p else d4385 p
theorem agree5261 (p q : Pattern) (h : Agree support p q) : d5261 p = d5261 q := by
  simp only [d5261, h 138 (by decide), agree12 p q h, agree4385 p q h]
theorem nonnegative5261 (p : Pattern) : 0 ≤ d5261 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4385 p)
def d5262 (p : Pattern) : Int := if p 116 then d5261 p else d5260 p
theorem agree5262 (p q : Pattern) (h : Agree support p q) : d5262 p = d5262 q := by
  simp only [d5262, h 116 (by decide), agree5261 p q h, agree5260 p q h]
theorem nonnegative5262 (p : Pattern) : 0 ≤ d5262 p :=
  nonnegative_ite (p 116) (nonnegative5261 p) (nonnegative5260 p)
def d5263 (p : Pattern) : Int := if p 115 then d5262 p else d5252 p
theorem agree5263 (p q : Pattern) (h : Agree support p q) : d5263 p = d5263 q := by
  simp only [d5263, h 115 (by decide), agree5262 p q h, agree5252 p q h]
theorem nonnegative5263 (p : Pattern) : 0 ≤ d5263 p :=
  nonnegative_ite (p 115) (nonnegative5262 p) (nonnegative5252 p)
def d5264 (p : Pattern) : Int := if p 71 then d5263 p else d5249 p
theorem agree5264 (p q : Pattern) (h : Agree support p q) : d5264 p = d5264 q := by
  simp only [d5264, h 71 (by decide), agree5263 p q h, agree5249 p q h]
theorem nonnegative5264 (p : Pattern) : 0 ≤ d5264 p :=
  nonnegative_ite (p 71) (nonnegative5263 p) (nonnegative5249 p)
def d5265 (p : Pattern) : Int := if p 49 then d5264 p else d5259 p
theorem agree5265 (p q : Pattern) (h : Agree support p q) : d5265 p = d5265 q := by
  simp only [d5265, h 49 (by decide), agree5264 p q h, agree5259 p q h]
theorem nonnegative5265 (p : Pattern) : 0 ≤ d5265 p :=
  nonnegative_ite (p 49) (nonnegative5264 p) (nonnegative5259 p)
def d5266 (p : Pattern) : Int := if p 48 then d5265 p else d5254 p
theorem agree5266 (p q : Pattern) (h : Agree support p q) : d5266 p = d5266 q := by
  simp only [d5266, h 48 (by decide), agree5265 p q h, agree5254 p q h]
theorem nonnegative5266 (p : Pattern) : 0 ≤ d5266 p :=
  nonnegative_ite (p 48) (nonnegative5265 p) (nonnegative5254 p)
def d5267 (p : Pattern) : Int := if p 246 then d1 p else d0 p
theorem agree5267 (p q : Pattern) (h : Agree support p q) : d5267 p = d5267 q := by
  simp only [d5267, h 246 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative5267 (p : Pattern) : 0 ≤ d5267 p :=
  nonnegative_ite (p 246) (nonnegative1 p) (nonnegative0 p)
def d5268 (p : Pattern) : Int := if p 246 then d0 p else d1 p
theorem agree5268 (p q : Pattern) (h : Agree support p q) : d5268 p = d5268 q := by
  simp only [d5268, h 246 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative5268 (p : Pattern) : 0 ≤ d5268 p :=
  nonnegative_ite (p 246) (nonnegative0 p) (nonnegative1 p)
def d5269 (p : Pattern) : Int := if p 224 then d5268 p else d0 p
theorem agree5269 (p q : Pattern) (h : Agree support p q) : d5269 p = d5269 q := by
  simp only [d5269, h 224 (by decide), agree5268 p q h, agree0 p q h]
theorem nonnegative5269 (p : Pattern) : 0 ≤ d5269 p :=
  nonnegative_ite (p 224) (nonnegative5268 p) (nonnegative0 p)
def d5270 (p : Pattern) : Int := if p 204 then d12 p else d13 p
theorem agree5270 (p q : Pattern) (h : Agree support p q) : d5270 p = d5270 q := by
  simp only [d5270, h 204 (by decide), agree12 p q h, agree13 p q h]
theorem nonnegative5270 (p : Pattern) : 0 ≤ d5270 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative13 p)
def d5271 (p : Pattern) : Int := if p 182 then d5270 p else d13 p
theorem agree5271 (p q : Pattern) (h : Agree support p q) : d5271 p = d5271 q := by
  simp only [d5271, h 182 (by decide), agree5270 p q h, agree13 p q h]
theorem nonnegative5271 (p : Pattern) : 0 ≤ d5271 p :=
  nonnegative_ite (p 182) (nonnegative5270 p) (nonnegative13 p)
def d5272 (p : Pattern) : Int := if p 204 then d12 p else d17 p
theorem agree5272 (p q : Pattern) (h : Agree support p q) : d5272 p = d5272 q := by
  simp only [d5272, h 204 (by decide), agree12 p q h, agree17 p q h]
theorem nonnegative5272 (p : Pattern) : 0 ≤ d5272 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative17 p)
def d5273 (p : Pattern) : Int := if p 182 then d5272 p else d17 p
theorem agree5273 (p q : Pattern) (h : Agree support p q) : d5273 p = d5273 q := by
  simp only [d5273, h 182 (by decide), agree5272 p q h, agree17 p q h]
theorem nonnegative5273 (p : Pattern) : 0 ≤ d5273 p :=
  nonnegative_ite (p 182) (nonnegative5272 p) (nonnegative17 p)
def d5274 (p : Pattern) : Int := if p 163 then d5273 p else d5271 p
theorem agree5274 (p q : Pattern) (h : Agree support p q) : d5274 p = d5274 q := by
  simp only [d5274, h 163 (by decide), agree5273 p q h, agree5271 p q h]
theorem nonnegative5274 (p : Pattern) : 0 ≤ d5274 p :=
  nonnegative_ite (p 163) (nonnegative5273 p) (nonnegative5271 p)
def d5275 (p : Pattern) : Int := if p 162 then d5274 p else d5271 p
theorem agree5275 (p q : Pattern) (h : Agree support p q) : d5275 p = d5275 q := by
  simp only [d5275, h 162 (by decide), agree5274 p q h, agree5271 p q h]
theorem nonnegative5275 (p : Pattern) : 0 ≤ d5275 p :=
  nonnegative_ite (p 162) (nonnegative5274 p) (nonnegative5271 p)
def d5276 (p : Pattern) : Int := if p 204 then d12 p else d23 p
theorem agree5276 (p q : Pattern) (h : Agree support p q) : d5276 p = d5276 q := by
  simp only [d5276, h 204 (by decide), agree12 p q h, agree23 p q h]
theorem nonnegative5276 (p : Pattern) : 0 ≤ d5276 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative23 p)
def d5277 (p : Pattern) : Int := if p 182 then d5276 p else d23 p
theorem agree5277 (p q : Pattern) (h : Agree support p q) : d5277 p = d5277 q := by
  simp only [d5277, h 182 (by decide), agree5276 p q h, agree23 p q h]
theorem nonnegative5277 (p : Pattern) : 0 ≤ d5277 p :=
  nonnegative_ite (p 182) (nonnegative5276 p) (nonnegative23 p)
def d5278 (p : Pattern) : Int := if p 163 then d12 p else d5277 p
theorem agree5278 (p q : Pattern) (h : Agree support p q) : d5278 p = d5278 q := by
  simp only [d5278, h 163 (by decide), agree12 p q h, agree5277 p q h]
theorem nonnegative5278 (p : Pattern) : 0 ≤ d5278 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5277 p)
def d5279 (p : Pattern) : Int := if p 162 then d5278 p else d5274 p
theorem agree5279 (p q : Pattern) (h : Agree support p q) : d5279 p = d5279 q := by
  simp only [d5279, h 162 (by decide), agree5278 p q h, agree5274 p q h]
theorem nonnegative5279 (p : Pattern) : 0 ≤ d5279 p :=
  nonnegative_ite (p 162) (nonnegative5278 p) (nonnegative5274 p)
end NetHack.Sokoban22Refined85
