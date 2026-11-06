/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes59
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7200 (p : Pattern) : Int := if p 182 then d12 p else d1951 p
theorem agree7200 (p q : Pattern) (h : Agree support p q) : d7200 p = d7200 q := by
  simp only [d7200, h 182 (by decide), agree12 p q h, agree1951 p q h]
theorem nonnegative7200 (p : Pattern) : 0 ≤ d7200 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1951 p)
def d7201 (p : Pattern) : Int := if p 163 then d7088 p else d7200 p
theorem agree7201 (p q : Pattern) (h : Agree support p q) : d7201 p = d7201 q := by
  simp only [d7201, h 163 (by decide), agree7088 p q h, agree7200 p q h]
theorem nonnegative7201 (p : Pattern) : 0 ≤ d7201 p :=
  nonnegative_ite (p 163) (nonnegative7088 p) (nonnegative7200 p)
def d7202 (p : Pattern) : Int := if p 162 then d7201 p else d7110 p
theorem agree7202 (p q : Pattern) (h : Agree support p q) : d7202 p = d7202 q := by
  simp only [d7202, h 162 (by decide), agree7201 p q h, agree7110 p q h]
theorem nonnegative7202 (p : Pattern) : 0 ≤ d7202 p :=
  nonnegative_ite (p 162) (nonnegative7201 p) (nonnegative7110 p)
def d7203 (p : Pattern) : Int := if p 163 then d7088 p else d7111 p
theorem agree7203 (p q : Pattern) (h : Agree support p q) : d7203 p = d7203 q := by
  simp only [d7203, h 163 (by decide), agree7088 p q h, agree7111 p q h]
theorem nonnegative7203 (p : Pattern) : 0 ≤ d7203 p :=
  nonnegative_ite (p 163) (nonnegative7088 p) (nonnegative7111 p)
def d7204 (p : Pattern) : Int := if p 162 then d7084 p else d7203 p
theorem agree7204 (p q : Pattern) (h : Agree support p q) : d7204 p = d7204 q := by
  simp only [d7204, h 162 (by decide), agree7084 p q h, agree7203 p q h]
theorem nonnegative7204 (p : Pattern) : 0 ≤ d7204 p :=
  nonnegative_ite (p 162) (nonnegative7084 p) (nonnegative7203 p)
def d7205 (p : Pattern) : Int := if p 161 then d7204 p else d7202 p
theorem agree7205 (p q : Pattern) (h : Agree support p q) : d7205 p = d7205 q := by
  simp only [d7205, h 161 (by decide), agree7204 p q h, agree7202 p q h]
theorem nonnegative7205 (p : Pattern) : 0 ≤ d7205 p :=
  nonnegative_ite (p 161) (nonnegative7204 p) (nonnegative7202 p)
def d7206 (p : Pattern) : Int := if p 162 then d7187 p else d7101 p
theorem agree7206 (p q : Pattern) (h : Agree support p q) : d7206 p = d7206 q := by
  simp only [d7206, h 162 (by decide), agree7187 p q h, agree7101 p q h]
theorem nonnegative7206 (p : Pattern) : 0 ≤ d7206 p :=
  nonnegative_ite (p 162) (nonnegative7187 p) (nonnegative7101 p)
def d7207 (p : Pattern) : Int := if p 161 then d7124 p else d7206 p
theorem agree7207 (p q : Pattern) (h : Agree support p q) : d7207 p = d7207 q := by
  simp only [d7207, h 161 (by decide), agree7124 p q h, agree7206 p q h]
theorem nonnegative7207 (p : Pattern) : 0 ≤ d7207 p :=
  nonnegative_ite (p 161) (nonnegative7124 p) (nonnegative7206 p)
def d7208 (p : Pattern) : Int := if p 160 then d7207 p else d7205 p
theorem agree7208 (p q : Pattern) (h : Agree support p q) : d7208 p = d7208 q := by
  simp only [d7208, h 160 (by decide), agree7207 p q h, agree7205 p q h]
theorem nonnegative7208 (p : Pattern) : 0 ≤ d7208 p :=
  nonnegative_ite (p 160) (nonnegative7207 p) (nonnegative7205 p)
def d7209 (p : Pattern) : Int := if p 182 then d12 p else d3176 p
theorem agree7209 (p q : Pattern) (h : Agree support p q) : d7209 p = d7209 q := by
  simp only [d7209, h 182 (by decide), agree12 p q h, agree3176 p q h]
theorem nonnegative7209 (p : Pattern) : 0 ≤ d7209 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3176 p)
def d7210 (p : Pattern) : Int := if p 163 then d7209 p else d7200 p
theorem agree7210 (p q : Pattern) (h : Agree support p q) : d7210 p = d7210 q := by
  simp only [d7210, h 163 (by decide), agree7209 p q h, agree7200 p q h]
theorem nonnegative7210 (p : Pattern) : 0 ≤ d7210 p :=
  nonnegative_ite (p 163) (nonnegative7209 p) (nonnegative7200 p)
def d7211 (p : Pattern) : Int := if p 182 then d12 p else d2136 p
theorem agree7211 (p q : Pattern) (h : Agree support p q) : d7211 p = d7211 q := by
  simp only [d7211, h 182 (by decide), agree12 p q h, agree2136 p q h]
theorem nonnegative7211 (p : Pattern) : 0 ≤ d7211 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2136 p)
def d7212 (p : Pattern) : Int := if p 163 then d12 p else d7211 p
theorem agree7212 (p q : Pattern) (h : Agree support p q) : d7212 p = d7212 q := by
  simp only [d7212, h 163 (by decide), agree12 p q h, agree7211 p q h]
theorem nonnegative7212 (p : Pattern) : 0 ≤ d7212 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7211 p)
def d7213 (p : Pattern) : Int := if p 162 then d7212 p else d7210 p
theorem agree7213 (p q : Pattern) (h : Agree support p q) : d7213 p = d7213 q := by
  simp only [d7213, h 162 (by decide), agree7212 p q h, agree7210 p q h]
theorem nonnegative7213 (p : Pattern) : 0 ≤ d7213 p :=
  nonnegative_ite (p 162) (nonnegative7212 p) (nonnegative7210 p)
def d7214 (p : Pattern) : Int := if p 161 then d7189 p else d7213 p
theorem agree7214 (p q : Pattern) (h : Agree support p q) : d7214 p = d7214 q := by
  simp only [d7214, h 161 (by decide), agree7189 p q h, agree7213 p q h]
theorem nonnegative7214 (p : Pattern) : 0 ≤ d7214 p :=
  nonnegative_ite (p 161) (nonnegative7189 p) (nonnegative7213 p)
def d7215 (p : Pattern) : Int := if p 162 then d7123 p else d7088 p
theorem agree7215 (p q : Pattern) (h : Agree support p q) : d7215 p = d7215 q := by
  simp only [d7215, h 162 (by decide), agree7123 p q h, agree7088 p q h]
theorem nonnegative7215 (p : Pattern) : 0 ≤ d7215 p :=
  nonnegative_ite (p 162) (nonnegative7123 p) (nonnegative7088 p)
def d7216 (p : Pattern) : Int := if p 162 then d12 p else d7019 p
theorem agree7216 (p q : Pattern) (h : Agree support p q) : d7216 p = d7216 q := by
  simp only [d7216, h 162 (by decide), agree12 p q h, agree7019 p q h]
theorem nonnegative7216 (p : Pattern) : 0 ≤ d7216 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7019 p)
def d7217 (p : Pattern) : Int := if p 161 then d7216 p else d7215 p
theorem agree7217 (p q : Pattern) (h : Agree support p q) : d7217 p = d7217 q := by
  simp only [d7217, h 161 (by decide), agree7216 p q h, agree7215 p q h]
theorem nonnegative7217 (p : Pattern) : 0 ≤ d7217 p :=
  nonnegative_ite (p 161) (nonnegative7216 p) (nonnegative7215 p)
def d7218 (p : Pattern) : Int := if p 160 then d7217 p else d7214 p
theorem agree7218 (p q : Pattern) (h : Agree support p q) : d7218 p = d7218 q := by
  simp only [d7218, h 160 (by decide), agree7217 p q h, agree7214 p q h]
theorem nonnegative7218 (p : Pattern) : 0 ≤ d7218 p :=
  nonnegative_ite (p 160) (nonnegative7217 p) (nonnegative7214 p)
def d7219 (p : Pattern) : Int := if p 141 then d7218 p else d7208 p
theorem agree7219 (p q : Pattern) (h : Agree support p q) : d7219 p = d7219 q := by
  simp only [d7219, h 141 (by decide), agree7218 p q h, agree7208 p q h]
theorem nonnegative7219 (p : Pattern) : 0 ≤ d7219 p :=
  nonnegative_ite (p 141) (nonnegative7218 p) (nonnegative7208 p)
def d7220 (p : Pattern) : Int := if p 163 then d7087 p else d7111 p
theorem agree7220 (p q : Pattern) (h : Agree support p q) : d7220 p = d7220 q := by
  simp only [d7220, h 163 (by decide), agree7087 p q h, agree7111 p q h]
theorem nonnegative7220 (p : Pattern) : 0 ≤ d7220 p :=
  nonnegative_ite (p 163) (nonnegative7087 p) (nonnegative7111 p)
def d7221 (p : Pattern) : Int := if p 163 then d7035 p else d7101 p
theorem agree7221 (p q : Pattern) (h : Agree support p q) : d7221 p = d7221 q := by
  simp only [d7221, h 163 (by decide), agree7035 p q h, agree7101 p q h]
theorem nonnegative7221 (p : Pattern) : 0 ≤ d7221 p :=
  nonnegative_ite (p 163) (nonnegative7035 p) (nonnegative7101 p)
def d7222 (p : Pattern) : Int := if p 162 then d7221 p else d7220 p
theorem agree7222 (p q : Pattern) (h : Agree support p q) : d7222 p = d7222 q := by
  simp only [d7222, h 162 (by decide), agree7221 p q h, agree7220 p q h]
theorem nonnegative7222 (p : Pattern) : 0 ≤ d7222 p :=
  nonnegative_ite (p 162) (nonnegative7221 p) (nonnegative7220 p)
def d7223 (p : Pattern) : Int := if p 161 then d7106 p else d7222 p
theorem agree7223 (p q : Pattern) (h : Agree support p q) : d7223 p = d7223 q := by
  simp only [d7223, h 161 (by decide), agree7106 p q h, agree7222 p q h]
theorem nonnegative7223 (p : Pattern) : 0 ≤ d7223 p :=
  nonnegative_ite (p 161) (nonnegative7106 p) (nonnegative7222 p)
def d7224 (p : Pattern) : Int := if p 160 then d7125 p else d7223 p
theorem agree7224 (p q : Pattern) (h : Agree support p q) : d7224 p = d7224 q := by
  simp only [d7224, h 160 (by decide), agree7125 p q h, agree7223 p q h]
theorem nonnegative7224 (p : Pattern) : 0 ≤ d7224 p :=
  nonnegative_ite (p 160) (nonnegative7125 p) (nonnegative7223 p)
def d7225 (p : Pattern) : Int := if p 161 then d12 p else d7216 p
theorem agree7225 (p q : Pattern) (h : Agree support p q) : d7225 p = d7225 q := by
  simp only [d7225, h 161 (by decide), agree12 p q h, agree7216 p q h]
theorem nonnegative7225 (p : Pattern) : 0 ≤ d7225 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7216 p)
def d7226 (p : Pattern) : Int := if p 160 then d7225 p else d7207 p
theorem agree7226 (p q : Pattern) (h : Agree support p q) : d7226 p = d7226 q := by
  simp only [d7226, h 160 (by decide), agree7225 p q h, agree7207 p q h]
theorem nonnegative7226 (p : Pattern) : 0 ≤ d7226 p :=
  nonnegative_ite (p 160) (nonnegative7225 p) (nonnegative7207 p)
def d7227 (p : Pattern) : Int := if p 141 then d7226 p else d7224 p
theorem agree7227 (p q : Pattern) (h : Agree support p q) : d7227 p = d7227 q := by
  simp only [d7227, h 141 (by decide), agree7226 p q h, agree7224 p q h]
theorem nonnegative7227 (p : Pattern) : 0 ≤ d7227 p :=
  nonnegative_ite (p 141) (nonnegative7226 p) (nonnegative7224 p)
def d7228 (p : Pattern) : Int := if p 138 then d7227 p else d7219 p
theorem agree7228 (p q : Pattern) (h : Agree support p q) : d7228 p = d7228 q := by
  simp only [d7228, h 138 (by decide), agree7227 p q h, agree7219 p q h]
theorem nonnegative7228 (p : Pattern) : 0 ≤ d7228 p :=
  nonnegative_ite (p 138) (nonnegative7227 p) (nonnegative7219 p)
def d7229 (p : Pattern) : Int := if p 163 then d7018 p else d7101 p
theorem agree7229 (p q : Pattern) (h : Agree support p q) : d7229 p = d7229 q := by
  simp only [d7229, h 163 (by decide), agree7018 p q h, agree7101 p q h]
theorem nonnegative7229 (p : Pattern) : 0 ≤ d7229 p :=
  nonnegative_ite (p 163) (nonnegative7018 p) (nonnegative7101 p)
def d7230 (p : Pattern) : Int := if p 162 then d7229 p else d7220 p
theorem agree7230 (p q : Pattern) (h : Agree support p q) : d7230 p = d7230 q := by
  simp only [d7230, h 162 (by decide), agree7229 p q h, agree7220 p q h]
theorem nonnegative7230 (p : Pattern) : 0 ≤ d7230 p :=
  nonnegative_ite (p 162) (nonnegative7229 p) (nonnegative7220 p)
def d7231 (p : Pattern) : Int := if p 163 then d7018 p else d7088 p
theorem agree7231 (p q : Pattern) (h : Agree support p q) : d7231 p = d7231 q := by
  simp only [d7231, h 163 (by decide), agree7018 p q h, agree7088 p q h]
theorem nonnegative7231 (p : Pattern) : 0 ≤ d7231 p :=
  nonnegative_ite (p 163) (nonnegative7018 p) (nonnegative7088 p)
def d7232 (p : Pattern) : Int := if p 162 then d12 p else d7231 p
theorem agree7232 (p q : Pattern) (h : Agree support p q) : d7232 p = d7232 q := by
  simp only [d7232, h 162 (by decide), agree12 p q h, agree7231 p q h]
theorem nonnegative7232 (p : Pattern) : 0 ≤ d7232 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7231 p)
def d7233 (p : Pattern) : Int := if p 161 then d7232 p else d7230 p
theorem agree7233 (p q : Pattern) (h : Agree support p q) : d7233 p = d7233 q := by
  simp only [d7233, h 161 (by decide), agree7232 p q h, agree7230 p q h]
theorem nonnegative7233 (p : Pattern) : 0 ≤ d7233 p :=
  nonnegative_ite (p 161) (nonnegative7232 p) (nonnegative7230 p)
def d7234 (p : Pattern) : Int := if p 163 then d7035 p else d7115 p
theorem agree7234 (p q : Pattern) (h : Agree support p q) : d7234 p = d7234 q := by
  simp only [d7234, h 163 (by decide), agree7035 p q h, agree7115 p q h]
theorem nonnegative7234 (p : Pattern) : 0 ≤ d7234 p :=
  nonnegative_ite (p 163) (nonnegative7035 p) (nonnegative7115 p)
def d7235 (p : Pattern) : Int := if p 162 then d12 p else d7234 p
theorem agree7235 (p q : Pattern) (h : Agree support p q) : d7235 p = d7235 q := by
  simp only [d7235, h 162 (by decide), agree12 p q h, agree7234 p q h]
theorem nonnegative7235 (p : Pattern) : 0 ≤ d7235 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7234 p)
def d7236 (p : Pattern) : Int := if p 161 then d12 p else d7235 p
theorem agree7236 (p q : Pattern) (h : Agree support p q) : d7236 p = d7236 q := by
  simp only [d7236, h 161 (by decide), agree12 p q h, agree7235 p q h]
theorem nonnegative7236 (p : Pattern) : 0 ≤ d7236 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7235 p)
def d7237 (p : Pattern) : Int := if p 160 then d7236 p else d7233 p
theorem agree7237 (p q : Pattern) (h : Agree support p q) : d7237 p = d7237 q := by
  simp only [d7237, h 160 (by decide), agree7236 p q h, agree7233 p q h]
theorem nonnegative7237 (p : Pattern) : 0 ≤ d7237 p :=
  nonnegative_ite (p 160) (nonnegative7236 p) (nonnegative7233 p)
def d7238 (p : Pattern) : Int := if p 141 then d7226 p else d7237 p
theorem agree7238 (p q : Pattern) (h : Agree support p q) : d7238 p = d7238 q := by
  simp only [d7238, h 141 (by decide), agree7226 p q h, agree7237 p q h]
theorem nonnegative7238 (p : Pattern) : 0 ≤ d7238 p :=
  nonnegative_ite (p 141) (nonnegative7226 p) (nonnegative7237 p)
def d7239 (p : Pattern) : Int := if p 138 then d12 p else d7238 p
theorem agree7239 (p q : Pattern) (h : Agree support p q) : d7239 p = d7239 q := by
  simp only [d7239, h 138 (by decide), agree12 p q h, agree7238 p q h]
theorem nonnegative7239 (p : Pattern) : 0 ≤ d7239 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7238 p)
def d7240 (p : Pattern) : Int := if p 116 then d7239 p else d7228 p
theorem agree7240 (p q : Pattern) (h : Agree support p q) : d7240 p = d7240 q := by
  simp only [d7240, h 116 (by decide), agree7239 p q h, agree7228 p q h]
theorem nonnegative7240 (p : Pattern) : 0 ≤ d7240 p :=
  nonnegative_ite (p 116) (nonnegative7239 p) (nonnegative7228 p)
def d7241 (p : Pattern) : Int := if p 115 then d7240 p else d7199 p
theorem agree7241 (p q : Pattern) (h : Agree support p q) : d7241 p = d7241 q := by
  simp only [d7241, h 115 (by decide), agree7240 p q h, agree7199 p q h]
theorem nonnegative7241 (p : Pattern) : 0 ≤ d7241 p :=
  nonnegative_ite (p 115) (nonnegative7240 p) (nonnegative7199 p)
def d7242 (p : Pattern) : Int := if p 71 then d7241 p else d7079 p
theorem agree7242 (p q : Pattern) (h : Agree support p q) : d7242 p = d7242 q := by
  simp only [d7242, h 71 (by decide), agree7241 p q h, agree7079 p q h]
theorem nonnegative7242 (p : Pattern) : 0 ≤ d7242 p :=
  nonnegative_ite (p 71) (nonnegative7241 p) (nonnegative7079 p)
def d7243 (p : Pattern) : Int := if p 49 then d7242 p else d7182 p
theorem agree7243 (p q : Pattern) (h : Agree support p q) : d7243 p = d7243 q := by
  simp only [d7243, h 49 (by decide), agree7242 p q h, agree7182 p q h]
theorem nonnegative7243 (p : Pattern) : 0 ≤ d7243 p :=
  nonnegative_ite (p 49) (nonnegative7242 p) (nonnegative7182 p)
def d7244 (p : Pattern) : Int := if p 48 then d7243 p else d7139 p
theorem agree7244 (p q : Pattern) (h : Agree support p q) : d7244 p = d7244 q := by
  simp only [d7244, h 48 (by decide), agree7243 p q h, agree7139 p q h]
theorem nonnegative7244 (p : Pattern) : 0 ≤ d7244 p :=
  nonnegative_ite (p 48) (nonnegative7243 p) (nonnegative7139 p)
def d7245 (p : Pattern) : Int := if p 225 then d4 p else d0 p
theorem agree7245 (p q : Pattern) (h : Agree support p q) : d7245 p = d7245 q := by
  simp only [d7245, h 225 (by decide), agree4 p q h, agree0 p q h]
theorem nonnegative7245 (p : Pattern) : 0 ≤ d7245 p :=
  nonnegative_ite (p 225) (nonnegative4 p) (nonnegative0 p)
def d7246 (p : Pattern) : Int := if p 224 then d4 p else d7245 p
theorem agree7246 (p q : Pattern) (h : Agree support p q) : d7246 p = d7246 q := by
  simp only [d7246, h 224 (by decide), agree4 p q h, agree7245 p q h]
theorem nonnegative7246 (p : Pattern) : 0 ≤ d7246 p :=
  nonnegative_ite (p 224) (nonnegative4 p) (nonnegative7245 p)
def d7247 (p : Pattern) : Int := if p 204 then d7246 p else d0 p
theorem agree7247 (p q : Pattern) (h : Agree support p q) : d7247 p = d7247 q := by
  simp only [d7247, h 204 (by decide), agree7246 p q h, agree0 p q h]
theorem nonnegative7247 (p : Pattern) : 0 ≤ d7247 p :=
  nonnegative_ite (p 204) (nonnegative7246 p) (nonnegative0 p)
def d7248 (p : Pattern) : Int := if p 225 then d2 p else d0 p
theorem agree7248 (p q : Pattern) (h : Agree support p q) : d7248 p = d7248 q := by
  simp only [d7248, h 225 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative7248 (p : Pattern) : 0 ≤ d7248 p :=
  nonnegative_ite (p 225) (nonnegative2 p) (nonnegative0 p)
def d7249 (p : Pattern) : Int := if p 224 then d2 p else d7248 p
theorem agree7249 (p q : Pattern) (h : Agree support p q) : d7249 p = d7249 q := by
  simp only [d7249, h 224 (by decide), agree2 p q h, agree7248 p q h]
theorem nonnegative7249 (p : Pattern) : 0 ≤ d7249 p :=
  nonnegative_ite (p 224) (nonnegative2 p) (nonnegative7248 p)
def d7250 (p : Pattern) : Int := if p 204 then d12 p else d7249 p
theorem agree7250 (p q : Pattern) (h : Agree support p q) : d7250 p = d7250 q := by
  simp only [d7250, h 204 (by decide), agree12 p q h, agree7249 p q h]
theorem nonnegative7250 (p : Pattern) : 0 ≤ d7250 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7249 p)
def d7251 (p : Pattern) : Int := if p 182 then d7250 p else d7247 p
theorem agree7251 (p q : Pattern) (h : Agree support p q) : d7251 p = d7251 q := by
  simp only [d7251, h 182 (by decide), agree7250 p q h, agree7247 p q h]
theorem nonnegative7251 (p : Pattern) : 0 ≤ d7251 p :=
  nonnegative_ite (p 182) (nonnegative7250 p) (nonnegative7247 p)
def d7252 (p : Pattern) : Int := if p 225 then d8 p else d4 p
theorem agree7252 (p q : Pattern) (h : Agree support p q) : d7252 p = d7252 q := by
  simp only [d7252, h 225 (by decide), agree8 p q h, agree4 p q h]
theorem nonnegative7252 (p : Pattern) : 0 ≤ d7252 p :=
  nonnegative_ite (p 225) (nonnegative8 p) (nonnegative4 p)
def d7253 (p : Pattern) : Int := if p 224 then d8 p else d7252 p
theorem agree7253 (p q : Pattern) (h : Agree support p q) : d7253 p = d7253 q := by
  simp only [d7253, h 224 (by decide), agree8 p q h, agree7252 p q h]
theorem nonnegative7253 (p : Pattern) : 0 ≤ d7253 p :=
  nonnegative_ite (p 224) (nonnegative8 p) (nonnegative7252 p)
def d7254 (p : Pattern) : Int := if p 204 then d7253 p else d4 p
theorem agree7254 (p q : Pattern) (h : Agree support p q) : d7254 p = d7254 q := by
  simp only [d7254, h 204 (by decide), agree7253 p q h, agree4 p q h]
theorem nonnegative7254 (p : Pattern) : 0 ≤ d7254 p :=
  nonnegative_ite (p 204) (nonnegative7253 p) (nonnegative4 p)
def d7255 (p : Pattern) : Int := if p 225 then d6 p else d4 p
theorem agree7255 (p q : Pattern) (h : Agree support p q) : d7255 p = d7255 q := by
  simp only [d7255, h 225 (by decide), agree6 p q h, agree4 p q h]
theorem nonnegative7255 (p : Pattern) : 0 ≤ d7255 p :=
  nonnegative_ite (p 225) (nonnegative6 p) (nonnegative4 p)
def d7256 (p : Pattern) : Int := if p 224 then d6 p else d7255 p
theorem agree7256 (p q : Pattern) (h : Agree support p q) : d7256 p = d7256 q := by
  simp only [d7256, h 224 (by decide), agree6 p q h, agree7255 p q h]
theorem nonnegative7256 (p : Pattern) : 0 ≤ d7256 p :=
  nonnegative_ite (p 224) (nonnegative6 p) (nonnegative7255 p)
def d7257 (p : Pattern) : Int := if p 204 then d12 p else d7256 p
theorem agree7257 (p q : Pattern) (h : Agree support p q) : d7257 p = d7257 q := by
  simp only [d7257, h 204 (by decide), agree12 p q h, agree7256 p q h]
theorem nonnegative7257 (p : Pattern) : 0 ≤ d7257 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7256 p)
def d7258 (p : Pattern) : Int := if p 182 then d7257 p else d7254 p
theorem agree7258 (p q : Pattern) (h : Agree support p q) : d7258 p = d7258 q := by
  simp only [d7258, h 182 (by decide), agree7257 p q h, agree7254 p q h]
theorem nonnegative7258 (p : Pattern) : 0 ≤ d7258 p :=
  nonnegative_ite (p 182) (nonnegative7257 p) (nonnegative7254 p)
def d7259 (p : Pattern) : Int := if p 163 then d7258 p else d7251 p
theorem agree7259 (p q : Pattern) (h : Agree support p q) : d7259 p = d7259 q := by
  simp only [d7259, h 163 (by decide), agree7258 p q h, agree7251 p q h]
theorem nonnegative7259 (p : Pattern) : 0 ≤ d7259 p :=
  nonnegative_ite (p 163) (nonnegative7258 p) (nonnegative7251 p)
def d7260 (p : Pattern) : Int := if p 162 then d7259 p else d7251 p
theorem agree7260 (p q : Pattern) (h : Agree support p q) : d7260 p = d7260 q := by
  simp only [d7260, h 162 (by decide), agree7259 p q h, agree7251 p q h]
theorem nonnegative7260 (p : Pattern) : 0 ≤ d7260 p :=
  nonnegative_ite (p 162) (nonnegative7259 p) (nonnegative7251 p)
def d7261 (p : Pattern) : Int := if p 225 then d12 p else d9 p
theorem agree7261 (p q : Pattern) (h : Agree support p q) : d7261 p = d7261 q := by
  simp only [d7261, h 225 (by decide), agree12 p q h, agree9 p q h]
theorem nonnegative7261 (p : Pattern) : 0 ≤ d7261 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative9 p)
def d7262 (p : Pattern) : Int := if p 224 then d12 p else d7261 p
theorem agree7262 (p q : Pattern) (h : Agree support p q) : d7262 p = d7262 q := by
  simp only [d7262, h 224 (by decide), agree12 p q h, agree7261 p q h]
theorem nonnegative7262 (p : Pattern) : 0 ≤ d7262 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7261 p)
def d7263 (p : Pattern) : Int := if p 204 then d7262 p else d9 p
theorem agree7263 (p q : Pattern) (h : Agree support p q) : d7263 p = d7263 q := by
  simp only [d7263, h 204 (by decide), agree7262 p q h, agree9 p q h]
theorem nonnegative7263 (p : Pattern) : 0 ≤ d7263 p :=
  nonnegative_ite (p 204) (nonnegative7262 p) (nonnegative9 p)
def d7264 (p : Pattern) : Int := if p 225 then d11 p else d9 p
theorem agree7264 (p q : Pattern) (h : Agree support p q) : d7264 p = d7264 q := by
  simp only [d7264, h 225 (by decide), agree11 p q h, agree9 p q h]
theorem nonnegative7264 (p : Pattern) : 0 ≤ d7264 p :=
  nonnegative_ite (p 225) (nonnegative11 p) (nonnegative9 p)
def d7265 (p : Pattern) : Int := if p 224 then d11 p else d7264 p
theorem agree7265 (p q : Pattern) (h : Agree support p q) : d7265 p = d7265 q := by
  simp only [d7265, h 224 (by decide), agree11 p q h, agree7264 p q h]
theorem nonnegative7265 (p : Pattern) : 0 ≤ d7265 p :=
  nonnegative_ite (p 224) (nonnegative11 p) (nonnegative7264 p)
def d7266 (p : Pattern) : Int := if p 204 then d12 p else d7265 p
theorem agree7266 (p q : Pattern) (h : Agree support p q) : d7266 p = d7266 q := by
  simp only [d7266, h 204 (by decide), agree12 p q h, agree7265 p q h]
theorem nonnegative7266 (p : Pattern) : 0 ≤ d7266 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7265 p)
def d7267 (p : Pattern) : Int := if p 182 then d7266 p else d7263 p
theorem agree7267 (p q : Pattern) (h : Agree support p q) : d7267 p = d7267 q := by
  simp only [d7267, h 182 (by decide), agree7266 p q h, agree7263 p q h]
theorem nonnegative7267 (p : Pattern) : 0 ≤ d7267 p :=
  nonnegative_ite (p 182) (nonnegative7266 p) (nonnegative7263 p)
def d7268 (p : Pattern) : Int := if p 163 then d12 p else d7267 p
theorem agree7268 (p q : Pattern) (h : Agree support p q) : d7268 p = d7268 q := by
  simp only [d7268, h 163 (by decide), agree12 p q h, agree7267 p q h]
theorem nonnegative7268 (p : Pattern) : 0 ≤ d7268 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7267 p)
def d7269 (p : Pattern) : Int := if p 162 then d7268 p else d7259 p
theorem agree7269 (p q : Pattern) (h : Agree support p q) : d7269 p = d7269 q := by
  simp only [d7269, h 162 (by decide), agree7268 p q h, agree7259 p q h]
theorem nonnegative7269 (p : Pattern) : 0 ≤ d7269 p :=
  nonnegative_ite (p 162) (nonnegative7268 p) (nonnegative7259 p)
def d7270 (p : Pattern) : Int := if p 161 then d7269 p else d7260 p
theorem agree7270 (p q : Pattern) (h : Agree support p q) : d7270 p = d7270 q := by
  simp only [d7270, h 161 (by decide), agree7269 p q h, agree7260 p q h]
theorem nonnegative7270 (p : Pattern) : 0 ≤ d7270 p :=
  nonnegative_ite (p 161) (nonnegative7269 p) (nonnegative7260 p)
def d7271 (p : Pattern) : Int := if p 225 then d6 p else d0 p
theorem agree7271 (p q : Pattern) (h : Agree support p q) : d7271 p = d7271 q := by
  simp only [d7271, h 225 (by decide), agree6 p q h, agree0 p q h]
theorem nonnegative7271 (p : Pattern) : 0 ≤ d7271 p :=
  nonnegative_ite (p 225) (nonnegative6 p) (nonnegative0 p)
def d7272 (p : Pattern) : Int := if p 225 then d9 p else d4 p
theorem agree7272 (p q : Pattern) (h : Agree support p q) : d7272 p = d7272 q := by
  simp only [d7272, h 225 (by decide), agree9 p q h, agree4 p q h]
theorem nonnegative7272 (p : Pattern) : 0 ≤ d7272 p :=
  nonnegative_ite (p 225) (nonnegative9 p) (nonnegative4 p)
def d7273 (p : Pattern) : Int := if p 224 then d7272 p else d7271 p
theorem agree7273 (p q : Pattern) (h : Agree support p q) : d7273 p = d7273 q := by
  simp only [d7273, h 224 (by decide), agree7272 p q h, agree7271 p q h]
theorem nonnegative7273 (p : Pattern) : 0 ≤ d7273 p :=
  nonnegative_ite (p 224) (nonnegative7272 p) (nonnegative7271 p)
def d7274 (p : Pattern) : Int := if p 204 then d7273 p else d0 p
theorem agree7274 (p q : Pattern) (h : Agree support p q) : d7274 p = d7274 q := by
  simp only [d7274, h 204 (by decide), agree7273 p q h, agree0 p q h]
theorem nonnegative7274 (p : Pattern) : 0 ≤ d7274 p :=
  nonnegative_ite (p 204) (nonnegative7273 p) (nonnegative0 p)
def d7275 (p : Pattern) : Int := if p 225 then d8 p else d2 p
theorem agree7275 (p q : Pattern) (h : Agree support p q) : d7275 p = d7275 q := by
  simp only [d7275, h 225 (by decide), agree8 p q h, agree2 p q h]
theorem nonnegative7275 (p : Pattern) : 0 ≤ d7275 p :=
  nonnegative_ite (p 225) (nonnegative8 p) (nonnegative2 p)
def d7276 (p : Pattern) : Int := if p 225 then d11 p else d6 p
theorem agree7276 (p q : Pattern) (h : Agree support p q) : d7276 p = d7276 q := by
  simp only [d7276, h 225 (by decide), agree11 p q h, agree6 p q h]
theorem nonnegative7276 (p : Pattern) : 0 ≤ d7276 p :=
  nonnegative_ite (p 225) (nonnegative11 p) (nonnegative6 p)
def d7277 (p : Pattern) : Int := if p 224 then d7276 p else d7275 p
theorem agree7277 (p q : Pattern) (h : Agree support p q) : d7277 p = d7277 q := by
  simp only [d7277, h 224 (by decide), agree7276 p q h, agree7275 p q h]
theorem nonnegative7277 (p : Pattern) : 0 ≤ d7277 p :=
  nonnegative_ite (p 224) (nonnegative7276 p) (nonnegative7275 p)
def d7278 (p : Pattern) : Int := if p 204 then d12 p else d7277 p
theorem agree7278 (p q : Pattern) (h : Agree support p q) : d7278 p = d7278 q := by
  simp only [d7278, h 204 (by decide), agree12 p q h, agree7277 p q h]
theorem nonnegative7278 (p : Pattern) : 0 ≤ d7278 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7277 p)
def d7279 (p : Pattern) : Int := if p 182 then d7278 p else d7274 p
theorem agree7279 (p q : Pattern) (h : Agree support p q) : d7279 p = d7279 q := by
  simp only [d7279, h 182 (by decide), agree7278 p q h, agree7274 p q h]
theorem nonnegative7279 (p : Pattern) : 0 ≤ d7279 p :=
  nonnegative_ite (p 182) (nonnegative7278 p) (nonnegative7274 p)
def d7280 (p : Pattern) : Int := if p 225 then d12 p else d6 p
theorem agree7280 (p q : Pattern) (h : Agree support p q) : d7280 p = d7280 q := by
  simp only [d7280, h 225 (by decide), agree12 p q h, agree6 p q h]
theorem nonnegative7280 (p : Pattern) : 0 ≤ d7280 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative6 p)
def d7281 (p : Pattern) : Int := if p 225 then d12 p else d10 p
theorem agree7281 (p q : Pattern) (h : Agree support p q) : d7281 p = d7281 q := by
  simp only [d7281, h 225 (by decide), agree12 p q h, agree10 p q h]
theorem nonnegative7281 (p : Pattern) : 0 ≤ d7281 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative10 p)
def d7282 (p : Pattern) : Int := if p 224 then d7281 p else d7280 p
theorem agree7282 (p q : Pattern) (h : Agree support p q) : d7282 p = d7282 q := by
  simp only [d7282, h 224 (by decide), agree7281 p q h, agree7280 p q h]
theorem nonnegative7282 (p : Pattern) : 0 ≤ d7282 p :=
  nonnegative_ite (p 224) (nonnegative7281 p) (nonnegative7280 p)
def d7283 (p : Pattern) : Int := if p 204 then d12 p else d7282 p
theorem agree7283 (p q : Pattern) (h : Agree support p q) : d7283 p = d7283 q := by
  simp only [d7283, h 204 (by decide), agree12 p q h, agree7282 p q h]
theorem nonnegative7283 (p : Pattern) : 0 ≤ d7283 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7282 p)
def d7284 (p : Pattern) : Int := if p 182 then d7283 p else d7274 p
theorem agree7284 (p q : Pattern) (h : Agree support p q) : d7284 p = d7284 q := by
  simp only [d7284, h 182 (by decide), agree7283 p q h, agree7274 p q h]
theorem nonnegative7284 (p : Pattern) : 0 ≤ d7284 p :=
  nonnegative_ite (p 182) (nonnegative7283 p) (nonnegative7274 p)
def d7285 (p : Pattern) : Int := if p 163 then d7284 p else d7279 p
theorem agree7285 (p q : Pattern) (h : Agree support p q) : d7285 p = d7285 q := by
  simp only [d7285, h 163 (by decide), agree7284 p q h, agree7279 p q h]
theorem nonnegative7285 (p : Pattern) : 0 ≤ d7285 p :=
  nonnegative_ite (p 163) (nonnegative7284 p) (nonnegative7279 p)
def d7286 (p : Pattern) : Int := if p 225 then d12 p else d11 p
theorem agree7286 (p q : Pattern) (h : Agree support p q) : d7286 p = d7286 q := by
  simp only [d7286, h 225 (by decide), agree12 p q h, agree11 p q h]
theorem nonnegative7286 (p : Pattern) : 0 ≤ d7286 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative11 p)
def d7287 (p : Pattern) : Int := if p 224 then d12 p else d7286 p
theorem agree7287 (p q : Pattern) (h : Agree support p q) : d7287 p = d7287 q := by
  simp only [d7287, h 224 (by decide), agree12 p q h, agree7286 p q h]
theorem nonnegative7287 (p : Pattern) : 0 ≤ d7287 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7286 p)
def d7288 (p : Pattern) : Int := if p 204 then d12 p else d7287 p
theorem agree7288 (p q : Pattern) (h : Agree support p q) : d7288 p = d7288 q := by
  simp only [d7288, h 204 (by decide), agree12 p q h, agree7287 p q h]
theorem nonnegative7288 (p : Pattern) : 0 ≤ d7288 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7287 p)
def d7289 (p : Pattern) : Int := if p 182 then d7288 p else d7274 p
theorem agree7289 (p q : Pattern) (h : Agree support p q) : d7289 p = d7289 q := by
  simp only [d7289, h 182 (by decide), agree7288 p q h, agree7274 p q h]
theorem nonnegative7289 (p : Pattern) : 0 ≤ d7289 p :=
  nonnegative_ite (p 182) (nonnegative7288 p) (nonnegative7274 p)
def d7290 (p : Pattern) : Int := if p 225 then d10 p else d4 p
theorem agree7290 (p q : Pattern) (h : Agree support p q) : d7290 p = d7290 q := by
  simp only [d7290, h 225 (by decide), agree10 p q h, agree4 p q h]
theorem nonnegative7290 (p : Pattern) : 0 ≤ d7290 p :=
  nonnegative_ite (p 225) (nonnegative10 p) (nonnegative4 p)
def d7291 (p : Pattern) : Int := if p 225 then d12 p else d8 p
theorem agree7291 (p q : Pattern) (h : Agree support p q) : d7291 p = d7291 q := by
  simp only [d7291, h 225 (by decide), agree12 p q h, agree8 p q h]
theorem nonnegative7291 (p : Pattern) : 0 ≤ d7291 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative8 p)
def d7292 (p : Pattern) : Int := if p 224 then d7291 p else d7290 p
theorem agree7292 (p q : Pattern) (h : Agree support p q) : d7292 p = d7292 q := by
  simp only [d7292, h 224 (by decide), agree7291 p q h, agree7290 p q h]
theorem nonnegative7292 (p : Pattern) : 0 ≤ d7292 p :=
  nonnegative_ite (p 224) (nonnegative7291 p) (nonnegative7290 p)
def d7293 (p : Pattern) : Int := if p 204 then d7292 p else d4 p
theorem agree7293 (p q : Pattern) (h : Agree support p q) : d7293 p = d7293 q := by
  simp only [d7293, h 204 (by decide), agree7292 p q h, agree4 p q h]
theorem nonnegative7293 (p : Pattern) : 0 ≤ d7293 p :=
  nonnegative_ite (p 204) (nonnegative7292 p) (nonnegative4 p)
def d7294 (p : Pattern) : Int := if p 182 then d12 p else d7293 p
theorem agree7294 (p q : Pattern) (h : Agree support p q) : d7294 p = d7294 q := by
  simp only [d7294, h 182 (by decide), agree12 p q h, agree7293 p q h]
theorem nonnegative7294 (p : Pattern) : 0 ≤ d7294 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7293 p)
def d7295 (p : Pattern) : Int := if p 163 then d7294 p else d7289 p
theorem agree7295 (p q : Pattern) (h : Agree support p q) : d7295 p = d7295 q := by
  simp only [d7295, h 163 (by decide), agree7294 p q h, agree7289 p q h]
theorem nonnegative7295 (p : Pattern) : 0 ≤ d7295 p :=
  nonnegative_ite (p 163) (nonnegative7294 p) (nonnegative7289 p)
def d7296 (p : Pattern) : Int := if p 162 then d7295 p else d7285 p
theorem agree7296 (p q : Pattern) (h : Agree support p q) : d7296 p = d7296 q := by
  simp only [d7296, h 162 (by decide), agree7295 p q h, agree7285 p q h]
theorem nonnegative7296 (p : Pattern) : 0 ≤ d7296 p :=
  nonnegative_ite (p 162) (nonnegative7295 p) (nonnegative7285 p)
def d7297 (p : Pattern) : Int := if p 182 then d12 p else d7274 p
theorem agree7297 (p q : Pattern) (h : Agree support p q) : d7297 p = d7297 q := by
  simp only [d7297, h 182 (by decide), agree12 p q h, agree7274 p q h]
theorem nonnegative7297 (p : Pattern) : 0 ≤ d7297 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7274 p)
def d7298 (p : Pattern) : Int := if p 163 then d7294 p else d7297 p
theorem agree7298 (p q : Pattern) (h : Agree support p q) : d7298 p = d7298 q := by
  simp only [d7298, h 163 (by decide), agree7294 p q h, agree7297 p q h]
theorem nonnegative7298 (p : Pattern) : 0 ≤ d7298 p :=
  nonnegative_ite (p 163) (nonnegative7294 p) (nonnegative7297 p)
def d7299 (p : Pattern) : Int := if p 182 then d12 p else d7263 p
theorem agree7299 (p q : Pattern) (h : Agree support p q) : d7299 p = d7299 q := by
  simp only [d7299, h 182 (by decide), agree12 p q h, agree7263 p q h]
theorem nonnegative7299 (p : Pattern) : 0 ≤ d7299 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7263 p)
def d7300 (p : Pattern) : Int := if p 163 then d12 p else d7299 p
theorem agree7300 (p q : Pattern) (h : Agree support p q) : d7300 p = d7300 q := by
  simp only [d7300, h 163 (by decide), agree12 p q h, agree7299 p q h]
theorem nonnegative7300 (p : Pattern) : 0 ≤ d7300 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7299 p)
def d7301 (p : Pattern) : Int := if p 162 then d7300 p else d7298 p
theorem agree7301 (p q : Pattern) (h : Agree support p q) : d7301 p = d7301 q := by
  simp only [d7301, h 162 (by decide), agree7300 p q h, agree7298 p q h]
theorem nonnegative7301 (p : Pattern) : 0 ≤ d7301 p :=
  nonnegative_ite (p 162) (nonnegative7300 p) (nonnegative7298 p)
def d7302 (p : Pattern) : Int := if p 161 then d7301 p else d7296 p
theorem agree7302 (p q : Pattern) (h : Agree support p q) : d7302 p = d7302 q := by
  simp only [d7302, h 161 (by decide), agree7301 p q h, agree7296 p q h]
theorem nonnegative7302 (p : Pattern) : 0 ≤ d7302 p :=
  nonnegative_ite (p 161) (nonnegative7301 p) (nonnegative7296 p)
def d7303 (p : Pattern) : Int := if p 160 then d7302 p else d7270 p
theorem agree7303 (p q : Pattern) (h : Agree support p q) : d7303 p = d7303 q := by
  simp only [d7303, h 160 (by decide), agree7302 p q h, agree7270 p q h]
theorem nonnegative7303 (p : Pattern) : 0 ≤ d7303 p :=
  nonnegative_ite (p 160) (nonnegative7302 p) (nonnegative7270 p)
def d7304 (p : Pattern) : Int := if p 225 then d6 p else d2 p
theorem agree7304 (p q : Pattern) (h : Agree support p q) : d7304 p = d7304 q := by
  simp only [d7304, h 225 (by decide), agree6 p q h, agree2 p q h]
theorem nonnegative7304 (p : Pattern) : 0 ≤ d7304 p :=
  nonnegative_ite (p 225) (nonnegative6 p) (nonnegative2 p)
def d7305 (p : Pattern) : Int := if p 224 then d6 p else d7304 p
theorem agree7305 (p q : Pattern) (h : Agree support p q) : d7305 p = d7305 q := by
  simp only [d7305, h 224 (by decide), agree6 p q h, agree7304 p q h]
theorem nonnegative7305 (p : Pattern) : 0 ≤ d7305 p :=
  nonnegative_ite (p 224) (nonnegative6 p) (nonnegative7304 p)
def d7306 (p : Pattern) : Int := if p 204 then d7305 p else d2 p
theorem agree7306 (p q : Pattern) (h : Agree support p q) : d7306 p = d7306 q := by
  simp only [d7306, h 204 (by decide), agree7305 p q h, agree2 p q h]
theorem nonnegative7306 (p : Pattern) : 0 ≤ d7306 p :=
  nonnegative_ite (p 204) (nonnegative7305 p) (nonnegative2 p)
def d7307 (p : Pattern) : Int := if p 225 then d4 p else d2 p
theorem agree7307 (p q : Pattern) (h : Agree support p q) : d7307 p = d7307 q := by
  simp only [d7307, h 225 (by decide), agree4 p q h, agree2 p q h]
theorem nonnegative7307 (p : Pattern) : 0 ≤ d7307 p :=
  nonnegative_ite (p 225) (nonnegative4 p) (nonnegative2 p)
def d7308 (p : Pattern) : Int := if p 224 then d4 p else d7307 p
theorem agree7308 (p q : Pattern) (h : Agree support p q) : d7308 p = d7308 q := by
  simp only [d7308, h 224 (by decide), agree4 p q h, agree7307 p q h]
theorem nonnegative7308 (p : Pattern) : 0 ≤ d7308 p :=
  nonnegative_ite (p 224) (nonnegative4 p) (nonnegative7307 p)
def d7309 (p : Pattern) : Int := if p 204 then d12 p else d7308 p
theorem agree7309 (p q : Pattern) (h : Agree support p q) : d7309 p = d7309 q := by
  simp only [d7309, h 204 (by decide), agree12 p q h, agree7308 p q h]
theorem nonnegative7309 (p : Pattern) : 0 ≤ d7309 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7308 p)
def d7310 (p : Pattern) : Int := if p 182 then d7309 p else d7306 p
theorem agree7310 (p q : Pattern) (h : Agree support p q) : d7310 p = d7310 q := by
  simp only [d7310, h 182 (by decide), agree7309 p q h, agree7306 p q h]
theorem nonnegative7310 (p : Pattern) : 0 ≤ d7310 p :=
  nonnegative_ite (p 182) (nonnegative7309 p) (nonnegative7306 p)
def d7311 (p : Pattern) : Int := if p 163 then d7310 p else d7251 p
theorem agree7311 (p q : Pattern) (h : Agree support p q) : d7311 p = d7311 q := by
  simp only [d7311, h 163 (by decide), agree7310 p q h, agree7251 p q h]
theorem nonnegative7311 (p : Pattern) : 0 ≤ d7311 p :=
  nonnegative_ite (p 163) (nonnegative7310 p) (nonnegative7251 p)
def d7312 (p : Pattern) : Int := if p 163 then d7267 p else d7258 p
theorem agree7312 (p q : Pattern) (h : Agree support p q) : d7312 p = d7312 q := by
  simp only [d7312, h 163 (by decide), agree7267 p q h, agree7258 p q h]
theorem nonnegative7312 (p : Pattern) : 0 ≤ d7312 p :=
  nonnegative_ite (p 163) (nonnegative7267 p) (nonnegative7258 p)
def d7313 (p : Pattern) : Int := if p 162 then d7312 p else d7311 p
theorem agree7313 (p q : Pattern) (h : Agree support p q) : d7313 p = d7313 q := by
  simp only [d7313, h 162 (by decide), agree7312 p q h, agree7311 p q h]
theorem nonnegative7313 (p : Pattern) : 0 ≤ d7313 p :=
  nonnegative_ite (p 162) (nonnegative7312 p) (nonnegative7311 p)
def d7314 (p : Pattern) : Int := if p 224 then d12 p else d7281 p
theorem agree7314 (p q : Pattern) (h : Agree support p q) : d7314 p = d7314 q := by
  simp only [d7314, h 224 (by decide), agree12 p q h, agree7281 p q h]
theorem nonnegative7314 (p : Pattern) : 0 ≤ d7314 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7281 p)
def d7315 (p : Pattern) : Int := if p 204 then d7314 p else d10 p
theorem agree7315 (p q : Pattern) (h : Agree support p q) : d7315 p = d7315 q := by
  simp only [d7315, h 204 (by decide), agree7314 p q h, agree10 p q h]
theorem nonnegative7315 (p : Pattern) : 0 ≤ d7315 p :=
  nonnegative_ite (p 204) (nonnegative7314 p) (nonnegative10 p)
def d7316 (p : Pattern) : Int := if p 204 then d12 p else d7314 p
theorem agree7316 (p q : Pattern) (h : Agree support p q) : d7316 p = d7316 q := by
  simp only [d7316, h 204 (by decide), agree12 p q h, agree7314 p q h]
theorem nonnegative7316 (p : Pattern) : 0 ≤ d7316 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7314 p)
def d7317 (p : Pattern) : Int := if p 182 then d7316 p else d7315 p
theorem agree7317 (p q : Pattern) (h : Agree support p q) : d7317 p = d7317 q := by
  simp only [d7317, h 182 (by decide), agree7316 p q h, agree7315 p q h]
theorem nonnegative7317 (p : Pattern) : 0 ≤ d7317 p :=
  nonnegative_ite (p 182) (nonnegative7316 p) (nonnegative7315 p)
def d7318 (p : Pattern) : Int := if p 163 then d7317 p else d7258 p
theorem agree7318 (p q : Pattern) (h : Agree support p q) : d7318 p = d7318 q := by
  simp only [d7318, h 163 (by decide), agree7317 p q h, agree7258 p q h]
theorem nonnegative7318 (p : Pattern) : 0 ≤ d7318 p :=
  nonnegative_ite (p 163) (nonnegative7317 p) (nonnegative7258 p)
def d7319 (p : Pattern) : Int := if p 204 then d7287 p else d11 p
theorem agree7319 (p q : Pattern) (h : Agree support p q) : d7319 p = d7319 q := by
  simp only [d7319, h 204 (by decide), agree7287 p q h, agree11 p q h]
theorem nonnegative7319 (p : Pattern) : 0 ≤ d7319 p :=
  nonnegative_ite (p 204) (nonnegative7287 p) (nonnegative11 p)
end NetHack.Sokoban22Refined85
