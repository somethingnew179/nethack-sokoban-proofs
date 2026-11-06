/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes34
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4200 (p : Pattern) : Int := if p 71 then d4199 p else d88 p
theorem agree4200 (p q : Pattern) (h : Agree support p q) : d4200 p = d4200 q := by
  simp only [d4200, h 71 (by decide), agree4199 p q h, agree88 p q h]
theorem nonnegative4200 (p : Pattern) : 0 ≤ d4200 p :=
  nonnegative_ite (p 71) (nonnegative4199 p) (nonnegative88 p)
def d4201 (p : Pattern) : Int := if p 49 then d4200 p else d88 p
theorem agree4201 (p q : Pattern) (h : Agree support p q) : d4201 p = d4201 q := by
  simp only [d4201, h 49 (by decide), agree4200 p q h, agree88 p q h]
theorem nonnegative4201 (p : Pattern) : 0 ≤ d4201 p :=
  nonnegative_ite (p 49) (nonnegative4200 p) (nonnegative88 p)
def d4202 (p : Pattern) : Int := if p 48 then d4201 p else d4198 p
theorem agree4202 (p q : Pattern) (h : Agree support p q) : d4202 p = d4202 q := by
  simp only [d4202, h 48 (by decide), agree4201 p q h, agree4198 p q h]
theorem nonnegative4202 (p : Pattern) : 0 ≤ d4202 p :=
  nonnegative_ite (p 48) (nonnegative4201 p) (nonnegative4198 p)
def d4203 (p : Pattern) : Int := if p 138 then d0 p else d4117 p
theorem agree4203 (p q : Pattern) (h : Agree support p q) : d4203 p = d4203 q := by
  simp only [d4203, h 138 (by decide), agree0 p q h, agree4117 p q h]
theorem nonnegative4203 (p : Pattern) : 0 ≤ d4203 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative4117 p)
def d4204 (p : Pattern) : Int := if p 138 then d0 p else d4116 p
theorem agree4204 (p q : Pattern) (h : Agree support p q) : d4204 p = d4204 q := by
  simp only [d4204, h 138 (by decide), agree0 p q h, agree4116 p q h]
theorem nonnegative4204 (p : Pattern) : 0 ≤ d4204 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative4116 p)
def d4205 (p : Pattern) : Int := if p 182 then d1 p else d0 p
theorem agree4205 (p q : Pattern) (h : Agree support p q) : d4205 p = d4205 q := by
  simp only [d4205, h 182 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4205 (p : Pattern) : 0 ≤ d4205 p :=
  nonnegative_ite (p 182) (nonnegative1 p) (nonnegative0 p)
def d4206 (p : Pattern) : Int := if p 182 then d0 p else d1 p
theorem agree4206 (p q : Pattern) (h : Agree support p q) : d4206 p = d4206 q := by
  simp only [d4206, h 182 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4206 (p : Pattern) : 0 ≤ d4206 p :=
  nonnegative_ite (p 182) (nonnegative0 p) (nonnegative1 p)
def d4207 (p : Pattern) : Int := if p 160 then d4206 p else d0 p
theorem agree4207 (p q : Pattern) (h : Agree support p q) : d4207 p = d4207 q := by
  simp only [d4207, h 160 (by decide), agree4206 p q h, agree0 p q h]
theorem nonnegative4207 (p : Pattern) : 0 ≤ d4207 p :=
  nonnegative_ite (p 160) (nonnegative4206 p) (nonnegative0 p)
def d4208 (p : Pattern) : Int := if p 138 then d0 p else d4207 p
theorem agree4208 (p q : Pattern) (h : Agree support p q) : d4208 p = d4208 q := by
  simp only [d4208, h 138 (by decide), agree0 p q h, agree4207 p q h]
theorem nonnegative4208 (p : Pattern) : 0 ≤ d4208 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative4207 p)
def d4209 (p : Pattern) : Int := if p 163 then d19 p else d15 p
theorem agree4209 (p q : Pattern) (h : Agree support p q) : d4209 p = d4209 q := by
  simp only [d4209, h 163 (by decide), agree19 p q h, agree15 p q h]
theorem nonnegative4209 (p : Pattern) : 0 ≤ d4209 p :=
  nonnegative_ite (p 163) (nonnegative19 p) (nonnegative15 p)
def d4210 (p : Pattern) : Int := if p 162 then d4209 p else d15 p
theorem agree4210 (p q : Pattern) (h : Agree support p q) : d4210 p = d4210 q := by
  simp only [d4210, h 162 (by decide), agree4209 p q h, agree15 p q h]
theorem nonnegative4210 (p : Pattern) : 0 ≤ d4210 p :=
  nonnegative_ite (p 162) (nonnegative4209 p) (nonnegative15 p)
def d4211 (p : Pattern) : Int := if p 163 then d12 p else d25 p
theorem agree4211 (p q : Pattern) (h : Agree support p q) : d4211 p = d4211 q := by
  simp only [d4211, h 163 (by decide), agree12 p q h, agree25 p q h]
theorem nonnegative4211 (p : Pattern) : 0 ≤ d4211 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative25 p)
def d4212 (p : Pattern) : Int := if p 162 then d4211 p else d4209 p
theorem agree4212 (p q : Pattern) (h : Agree support p q) : d4212 p = d4212 q := by
  simp only [d4212, h 162 (by decide), agree4211 p q h, agree4209 p q h]
theorem nonnegative4212 (p : Pattern) : 0 ≤ d4212 p :=
  nonnegative_ite (p 162) (nonnegative4211 p) (nonnegative4209 p)
def d4213 (p : Pattern) : Int := if p 161 then d4212 p else d4210 p
theorem agree4213 (p q : Pattern) (h : Agree support p q) : d4213 p = d4213 q := by
  simp only [d4213, h 161 (by decide), agree4212 p q h, agree4210 p q h]
theorem nonnegative4213 (p : Pattern) : 0 ≤ d4213 p :=
  nonnegative_ite (p 161) (nonnegative4212 p) (nonnegative4210 p)
def d4214 (p : Pattern) : Int := if p 163 then d32 p else d15 p
theorem agree4214 (p q : Pattern) (h : Agree support p q) : d4214 p = d4214 q := by
  simp only [d4214, h 163 (by decide), agree32 p q h, agree15 p q h]
theorem nonnegative4214 (p : Pattern) : 0 ≤ d4214 p :=
  nonnegative_ite (p 163) (nonnegative32 p) (nonnegative15 p)
def d4215 (p : Pattern) : Int := if p 163 then d25 p else d19 p
theorem agree4215 (p q : Pattern) (h : Agree support p q) : d4215 p = d4215 q := by
  simp only [d4215, h 163 (by decide), agree25 p q h, agree19 p q h]
theorem nonnegative4215 (p : Pattern) : 0 ≤ d4215 p :=
  nonnegative_ite (p 163) (nonnegative25 p) (nonnegative19 p)
def d4216 (p : Pattern) : Int := if p 162 then d4215 p else d4214 p
theorem agree4216 (p q : Pattern) (h : Agree support p q) : d4216 p = d4216 q := by
  simp only [d4216, h 162 (by decide), agree4215 p q h, agree4214 p q h]
theorem nonnegative4216 (p : Pattern) : 0 ≤ d4216 p :=
  nonnegative_ite (p 162) (nonnegative4215 p) (nonnegative4214 p)
def d4217 (p : Pattern) : Int := if p 163 then d59 p else d19 p
theorem agree4217 (p q : Pattern) (h : Agree support p q) : d4217 p = d4217 q := by
  simp only [d4217, h 163 (by decide), agree59 p q h, agree19 p q h]
theorem nonnegative4217 (p : Pattern) : 0 ≤ d4217 p :=
  nonnegative_ite (p 163) (nonnegative59 p) (nonnegative19 p)
def d4218 (p : Pattern) : Int := if p 163 then d12 p else d41 p
theorem agree4218 (p q : Pattern) (h : Agree support p q) : d4218 p = d4218 q := by
  simp only [d4218, h 163 (by decide), agree12 p q h, agree41 p q h]
theorem nonnegative4218 (p : Pattern) : 0 ≤ d4218 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative41 p)
def d4219 (p : Pattern) : Int := if p 162 then d4218 p else d4217 p
theorem agree4219 (p q : Pattern) (h : Agree support p q) : d4219 p = d4219 q := by
  simp only [d4219, h 162 (by decide), agree4218 p q h, agree4217 p q h]
theorem nonnegative4219 (p : Pattern) : 0 ≤ d4219 p :=
  nonnegative_ite (p 162) (nonnegative4218 p) (nonnegative4217 p)
def d4220 (p : Pattern) : Int := if p 161 then d4219 p else d4216 p
theorem agree4220 (p q : Pattern) (h : Agree support p q) : d4220 p = d4220 q := by
  simp only [d4220, h 161 (by decide), agree4219 p q h, agree4216 p q h]
theorem nonnegative4220 (p : Pattern) : 0 ≤ d4220 p :=
  nonnegative_ite (p 161) (nonnegative4219 p) (nonnegative4216 p)
def d4221 (p : Pattern) : Int := if p 141 then d4220 p else d4213 p
theorem agree4221 (p q : Pattern) (h : Agree support p q) : d4221 p = d4221 q := by
  simp only [d4221, h 141 (by decide), agree4220 p q h, agree4213 p q h]
theorem nonnegative4221 (p : Pattern) : 0 ≤ d4221 p :=
  nonnegative_ite (p 141) (nonnegative4220 p) (nonnegative4213 p)
def d4222 (p : Pattern) : Int := if p 163 then d41 p else d25 p
theorem agree4222 (p q : Pattern) (h : Agree support p q) : d4222 p = d4222 q := by
  simp only [d4222, h 163 (by decide), agree41 p q h, agree25 p q h]
theorem nonnegative4222 (p : Pattern) : 0 ≤ d4222 p :=
  nonnegative_ite (p 163) (nonnegative41 p) (nonnegative25 p)
def d4223 (p : Pattern) : Int := if p 162 then d4218 p else d4222 p
theorem agree4223 (p q : Pattern) (h : Agree support p q) : d4223 p = d4223 q := by
  simp only [d4223, h 162 (by decide), agree4218 p q h, agree4222 p q h]
theorem nonnegative4223 (p : Pattern) : 0 ≤ d4223 p :=
  nonnegative_ite (p 162) (nonnegative4218 p) (nonnegative4222 p)
def d4224 (p : Pattern) : Int := if p 162 then d12 p else d4218 p
theorem agree4224 (p q : Pattern) (h : Agree support p q) : d4224 p = d4224 q := by
  simp only [d4224, h 162 (by decide), agree12 p q h, agree4218 p q h]
theorem nonnegative4224 (p : Pattern) : 0 ≤ d4224 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4218 p)
def d4225 (p : Pattern) : Int := if p 161 then d4224 p else d4223 p
theorem agree4225 (p q : Pattern) (h : Agree support p q) : d4225 p = d4225 q := by
  simp only [d4225, h 161 (by decide), agree4224 p q h, agree4223 p q h]
theorem nonnegative4225 (p : Pattern) : 0 ≤ d4225 p :=
  nonnegative_ite (p 161) (nonnegative4224 p) (nonnegative4223 p)
def d4226 (p : Pattern) : Int := if p 161 then d12 p else d4224 p
theorem agree4226 (p q : Pattern) (h : Agree support p q) : d4226 p = d4226 q := by
  simp only [d4226, h 161 (by decide), agree12 p q h, agree4224 p q h]
theorem nonnegative4226 (p : Pattern) : 0 ≤ d4226 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4224 p)
def d4227 (p : Pattern) : Int := if p 141 then d4226 p else d4225 p
theorem agree4227 (p q : Pattern) (h : Agree support p q) : d4227 p = d4227 q := by
  simp only [d4227, h 141 (by decide), agree4226 p q h, agree4225 p q h]
theorem nonnegative4227 (p : Pattern) : 0 ≤ d4227 p :=
  nonnegative_ite (p 141) (nonnegative4226 p) (nonnegative4225 p)
def d4228 (p : Pattern) : Int := if p 138 then d4227 p else d4221 p
theorem agree4228 (p q : Pattern) (h : Agree support p q) : d4228 p = d4228 q := by
  simp only [d4228, h 138 (by decide), agree4227 p q h, agree4221 p q h]
theorem nonnegative4228 (p : Pattern) : 0 ≤ d4228 p :=
  nonnegative_ite (p 138) (nonnegative4227 p) (nonnegative4221 p)
def d4229 (p : Pattern) : Int := if p 116 then d4228 p else d4221 p
theorem agree4229 (p q : Pattern) (h : Agree support p q) : d4229 p = d4229 q := by
  simp only [d4229, h 116 (by decide), agree4228 p q h, agree4221 p q h]
theorem nonnegative4229 (p : Pattern) : 0 ≤ d4229 p :=
  nonnegative_ite (p 116) (nonnegative4228 p) (nonnegative4221 p)
def d4230 (p : Pattern) : Int := if p 138 then d12 p else d4221 p
theorem agree4230 (p q : Pattern) (h : Agree support p q) : d4230 p = d4230 q := by
  simp only [d4230, h 138 (by decide), agree12 p q h, agree4221 p q h]
theorem nonnegative4230 (p : Pattern) : 0 ≤ d4230 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4221 p)
def d4231 (p : Pattern) : Int := if p 116 then d4230 p else d4221 p
theorem agree4231 (p q : Pattern) (h : Agree support p q) : d4231 p = d4231 q := by
  simp only [d4231, h 116 (by decide), agree4230 p q h, agree4221 p q h]
theorem nonnegative4231 (p : Pattern) : 0 ≤ d4231 p :=
  nonnegative_ite (p 116) (nonnegative4230 p) (nonnegative4221 p)
def d4232 (p : Pattern) : Int := if p 115 then d4231 p else d4229 p
theorem agree4232 (p q : Pattern) (h : Agree support p q) : d4232 p = d4232 q := by
  simp only [d4232, h 115 (by decide), agree4231 p q h, agree4229 p q h]
theorem nonnegative4232 (p : Pattern) : 0 ≤ d4232 p :=
  nonnegative_ite (p 115) (nonnegative4231 p) (nonnegative4229 p)
def d4233 (p : Pattern) : Int := if p 163 then d108 p else d104 p
theorem agree4233 (p q : Pattern) (h : Agree support p q) : d4233 p = d4233 q := by
  simp only [d4233, h 163 (by decide), agree108 p q h, agree104 p q h]
theorem nonnegative4233 (p : Pattern) : 0 ≤ d4233 p :=
  nonnegative_ite (p 163) (nonnegative108 p) (nonnegative104 p)
def d4234 (p : Pattern) : Int := if p 162 then d4233 p else d104 p
theorem agree4234 (p q : Pattern) (h : Agree support p q) : d4234 p = d4234 q := by
  simp only [d4234, h 162 (by decide), agree4233 p q h, agree104 p q h]
theorem nonnegative4234 (p : Pattern) : 0 ≤ d4234 p :=
  nonnegative_ite (p 162) (nonnegative4233 p) (nonnegative104 p)
def d4235 (p : Pattern) : Int := if p 163 then d12 p else d59 p
theorem agree4235 (p q : Pattern) (h : Agree support p q) : d4235 p = d4235 q := by
  simp only [d4235, h 163 (by decide), agree12 p q h, agree59 p q h]
theorem nonnegative4235 (p : Pattern) : 0 ≤ d4235 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative59 p)
def d4236 (p : Pattern) : Int := if p 162 then d4235 p else d4233 p
theorem agree4236 (p q : Pattern) (h : Agree support p q) : d4236 p = d4236 q := by
  simp only [d4236, h 162 (by decide), agree4235 p q h, agree4233 p q h]
theorem nonnegative4236 (p : Pattern) : 0 ≤ d4236 p :=
  nonnegative_ite (p 162) (nonnegative4235 p) (nonnegative4233 p)
def d4237 (p : Pattern) : Int := if p 161 then d4236 p else d4234 p
theorem agree4237 (p q : Pattern) (h : Agree support p q) : d4237 p = d4237 q := by
  simp only [d4237, h 161 (by decide), agree4236 p q h, agree4234 p q h]
theorem nonnegative4237 (p : Pattern) : 0 ≤ d4237 p :=
  nonnegative_ite (p 161) (nonnegative4236 p) (nonnegative4234 p)
def d4238 (p : Pattern) : Int := if p 163 then d117 p else d104 p
theorem agree4238 (p q : Pattern) (h : Agree support p q) : d4238 p = d4238 q := by
  simp only [d4238, h 163 (by decide), agree117 p q h, agree104 p q h]
theorem nonnegative4238 (p : Pattern) : 0 ≤ d4238 p :=
  nonnegative_ite (p 163) (nonnegative117 p) (nonnegative104 p)
def d4239 (p : Pattern) : Int := if p 163 then d59 p else d108 p
theorem agree4239 (p q : Pattern) (h : Agree support p q) : d4239 p = d4239 q := by
  simp only [d4239, h 163 (by decide), agree59 p q h, agree108 p q h]
theorem nonnegative4239 (p : Pattern) : 0 ≤ d4239 p :=
  nonnegative_ite (p 163) (nonnegative59 p) (nonnegative108 p)
def d4240 (p : Pattern) : Int := if p 162 then d4239 p else d4238 p
theorem agree4240 (p q : Pattern) (h : Agree support p q) : d4240 p = d4240 q := by
  simp only [d4240, h 162 (by decide), agree4239 p q h, agree4238 p q h]
theorem nonnegative4240 (p : Pattern) : 0 ≤ d4240 p :=
  nonnegative_ite (p 162) (nonnegative4239 p) (nonnegative4238 p)
def d4241 (p : Pattern) : Int := if p 163 then d41 p else d108 p
theorem agree4241 (p q : Pattern) (h : Agree support p q) : d4241 p = d4241 q := by
  simp only [d4241, h 163 (by decide), agree41 p q h, agree108 p q h]
theorem nonnegative4241 (p : Pattern) : 0 ≤ d4241 p :=
  nonnegative_ite (p 163) (nonnegative41 p) (nonnegative108 p)
def d4242 (p : Pattern) : Int := if p 162 then d12 p else d4241 p
theorem agree4242 (p q : Pattern) (h : Agree support p q) : d4242 p = d4242 q := by
  simp only [d4242, h 162 (by decide), agree12 p q h, agree4241 p q h]
theorem nonnegative4242 (p : Pattern) : 0 ≤ d4242 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4241 p)
def d4243 (p : Pattern) : Int := if p 161 then d4242 p else d4240 p
theorem agree4243 (p q : Pattern) (h : Agree support p q) : d4243 p = d4243 q := by
  simp only [d4243, h 161 (by decide), agree4242 p q h, agree4240 p q h]
theorem nonnegative4243 (p : Pattern) : 0 ≤ d4243 p :=
  nonnegative_ite (p 161) (nonnegative4242 p) (nonnegative4240 p)
def d4244 (p : Pattern) : Int := if p 141 then d4243 p else d4237 p
theorem agree4244 (p q : Pattern) (h : Agree support p q) : d4244 p = d4244 q := by
  simp only [d4244, h 141 (by decide), agree4243 p q h, agree4237 p q h]
theorem nonnegative4244 (p : Pattern) : 0 ≤ d4244 p :=
  nonnegative_ite (p 141) (nonnegative4243 p) (nonnegative4237 p)
def d4245 (p : Pattern) : Int := if p 162 then d12 p else d4235 p
theorem agree4245 (p q : Pattern) (h : Agree support p q) : d4245 p = d4245 q := by
  simp only [d4245, h 162 (by decide), agree12 p q h, agree4235 p q h]
theorem nonnegative4245 (p : Pattern) : 0 ≤ d4245 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4235 p)
def d4246 (p : Pattern) : Int := if p 161 then d12 p else d4245 p
theorem agree4246 (p q : Pattern) (h : Agree support p q) : d4246 p = d4246 q := by
  simp only [d4246, h 161 (by decide), agree12 p q h, agree4245 p q h]
theorem nonnegative4246 (p : Pattern) : 0 ≤ d4246 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4245 p)
def d4247 (p : Pattern) : Int := if p 141 then d12 p else d4246 p
theorem agree4247 (p q : Pattern) (h : Agree support p q) : d4247 p = d4247 q := by
  simp only [d4247, h 141 (by decide), agree12 p q h, agree4246 p q h]
theorem nonnegative4247 (p : Pattern) : 0 ≤ d4247 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative4246 p)
def d4248 (p : Pattern) : Int := if p 138 then d4247 p else d4244 p
theorem agree4248 (p q : Pattern) (h : Agree support p q) : d4248 p = d4248 q := by
  simp only [d4248, h 138 (by decide), agree4247 p q h, agree4244 p q h]
theorem nonnegative4248 (p : Pattern) : 0 ≤ d4248 p :=
  nonnegative_ite (p 138) (nonnegative4247 p) (nonnegative4244 p)
def d4249 (p : Pattern) : Int := if p 116 then d4248 p else d4244 p
theorem agree4249 (p q : Pattern) (h : Agree support p q) : d4249 p = d4249 q := by
  simp only [d4249, h 116 (by decide), agree4248 p q h, agree4244 p q h]
theorem nonnegative4249 (p : Pattern) : 0 ≤ d4249 p :=
  nonnegative_ite (p 116) (nonnegative4248 p) (nonnegative4244 p)
def d4250 (p : Pattern) : Int := if p 138 then d12 p else d4244 p
theorem agree4250 (p q : Pattern) (h : Agree support p q) : d4250 p = d4250 q := by
  simp only [d4250, h 138 (by decide), agree12 p q h, agree4244 p q h]
theorem nonnegative4250 (p : Pattern) : 0 ≤ d4250 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4244 p)
def d4251 (p : Pattern) : Int := if p 116 then d4250 p else d4244 p
theorem agree4251 (p q : Pattern) (h : Agree support p q) : d4251 p = d4251 q := by
  simp only [d4251, h 116 (by decide), agree4250 p q h, agree4244 p q h]
theorem nonnegative4251 (p : Pattern) : 0 ≤ d4251 p :=
  nonnegative_ite (p 116) (nonnegative4250 p) (nonnegative4244 p)
def d4252 (p : Pattern) : Int := if p 115 then d4251 p else d4249 p
theorem agree4252 (p q : Pattern) (h : Agree support p q) : d4252 p = d4252 q := by
  simp only [d4252, h 115 (by decide), agree4251 p q h, agree4249 p q h]
theorem nonnegative4252 (p : Pattern) : 0 ≤ d4252 p :=
  nonnegative_ite (p 115) (nonnegative4251 p) (nonnegative4249 p)
def d4253 (p : Pattern) : Int := if p 71 then d4252 p else d4232 p
theorem agree4253 (p q : Pattern) (h : Agree support p q) : d4253 p = d4253 q := by
  simp only [d4253, h 71 (by decide), agree4252 p q h, agree4232 p q h]
theorem nonnegative4253 (p : Pattern) : 0 ≤ d4253 p :=
  nonnegative_ite (p 71) (nonnegative4252 p) (nonnegative4232 p)
def d4254 (p : Pattern) : Int := if p 49 then d4253 p else d4232 p
theorem agree4254 (p q : Pattern) (h : Agree support p q) : d4254 p = d4254 q := by
  simp only [d4254, h 49 (by decide), agree4253 p q h, agree4232 p q h]
theorem nonnegative4254 (p : Pattern) : 0 ≤ d4254 p :=
  nonnegative_ite (p 49) (nonnegative4253 p) (nonnegative4232 p)
def d4255 (p : Pattern) : Int := if p 163 then d36 p else d32 p
theorem agree4255 (p q : Pattern) (h : Agree support p q) : d4255 p = d4255 q := by
  simp only [d4255, h 163 (by decide), agree36 p q h, agree32 p q h]
theorem nonnegative4255 (p : Pattern) : 0 ≤ d4255 p :=
  nonnegative_ite (p 163) (nonnegative36 p) (nonnegative32 p)
def d4256 (p : Pattern) : Int := if p 162 then d4255 p else d15 p
theorem agree4256 (p q : Pattern) (h : Agree support p q) : d4256 p = d4256 q := by
  simp only [d4256, h 162 (by decide), agree4255 p q h, agree15 p q h]
theorem nonnegative4256 (p : Pattern) : 0 ≤ d4256 p :=
  nonnegative_ite (p 162) (nonnegative4255 p) (nonnegative15 p)
def d4257 (p : Pattern) : Int := if p 162 then d4218 p else d4255 p
theorem agree4257 (p q : Pattern) (h : Agree support p q) : d4257 p = d4257 q := by
  simp only [d4257, h 162 (by decide), agree4218 p q h, agree4255 p q h]
theorem nonnegative4257 (p : Pattern) : 0 ≤ d4257 p :=
  nonnegative_ite (p 162) (nonnegative4218 p) (nonnegative4255 p)
def d4258 (p : Pattern) : Int := if p 161 then d4257 p else d4256 p
theorem agree4258 (p q : Pattern) (h : Agree support p q) : d4258 p = d4258 q := by
  simp only [d4258, h 161 (by decide), agree4257 p q h, agree4256 p q h]
theorem nonnegative4258 (p : Pattern) : 0 ≤ d4258 p :=
  nonnegative_ite (p 161) (nonnegative4257 p) (nonnegative4256 p)
def d4259 (p : Pattern) : Int := if p 163 then d41 p else d19 p
theorem agree4259 (p q : Pattern) (h : Agree support p q) : d4259 p = d4259 q := by
  simp only [d4259, h 163 (by decide), agree41 p q h, agree19 p q h]
theorem nonnegative4259 (p : Pattern) : 0 ≤ d4259 p :=
  nonnegative_ite (p 163) (nonnegative41 p) (nonnegative19 p)
def d4260 (p : Pattern) : Int := if p 162 then d4259 p else d32 p
theorem agree4260 (p q : Pattern) (h : Agree support p q) : d4260 p = d4260 q := by
  simp only [d4260, h 162 (by decide), agree4259 p q h, agree32 p q h]
theorem nonnegative4260 (p : Pattern) : 0 ≤ d4260 p :=
  nonnegative_ite (p 162) (nonnegative4259 p) (nonnegative32 p)
def d4261 (p : Pattern) : Int := if p 163 then d12 p else d36 p
theorem agree4261 (p q : Pattern) (h : Agree support p q) : d4261 p = d4261 q := by
  simp only [d4261, h 163 (by decide), agree12 p q h, agree36 p q h]
theorem nonnegative4261 (p : Pattern) : 0 ≤ d4261 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative36 p)
def d4262 (p : Pattern) : Int := if p 162 then d12 p else d4261 p
theorem agree4262 (p q : Pattern) (h : Agree support p q) : d4262 p = d4262 q := by
  simp only [d4262, h 162 (by decide), agree12 p q h, agree4261 p q h]
theorem nonnegative4262 (p : Pattern) : 0 ≤ d4262 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4261 p)
def d4263 (p : Pattern) : Int := if p 161 then d4262 p else d4260 p
theorem agree4263 (p q : Pattern) (h : Agree support p q) : d4263 p = d4263 q := by
  simp only [d4263, h 161 (by decide), agree4262 p q h, agree4260 p q h]
theorem nonnegative4263 (p : Pattern) : 0 ≤ d4263 p :=
  nonnegative_ite (p 161) (nonnegative4262 p) (nonnegative4260 p)
def d4264 (p : Pattern) : Int := if p 141 then d4263 p else d4258 p
theorem agree4264 (p q : Pattern) (h : Agree support p q) : d4264 p = d4264 q := by
  simp only [d4264, h 141 (by decide), agree4263 p q h, agree4258 p q h]
theorem nonnegative4264 (p : Pattern) : 0 ≤ d4264 p :=
  nonnegative_ite (p 141) (nonnegative4263 p) (nonnegative4258 p)
def d4265 (p : Pattern) : Int := if p 138 then d4264 p else d4221 p
theorem agree4265 (p q : Pattern) (h : Agree support p q) : d4265 p = d4265 q := by
  simp only [d4265, h 138 (by decide), agree4264 p q h, agree4221 p q h]
theorem nonnegative4265 (p : Pattern) : 0 ≤ d4265 p :=
  nonnegative_ite (p 138) (nonnegative4264 p) (nonnegative4221 p)
def d4266 (p : Pattern) : Int := if p 138 then d12 p else d4264 p
theorem agree4266 (p q : Pattern) (h : Agree support p q) : d4266 p = d4266 q := by
  simp only [d4266, h 138 (by decide), agree12 p q h, agree4264 p q h]
theorem nonnegative4266 (p : Pattern) : 0 ≤ d4266 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4264 p)
def d4267 (p : Pattern) : Int := if p 116 then d4266 p else d4265 p
theorem agree4267 (p q : Pattern) (h : Agree support p q) : d4267 p = d4267 q := by
  simp only [d4267, h 116 (by decide), agree4266 p q h, agree4265 p q h]
theorem nonnegative4267 (p : Pattern) : 0 ≤ d4267 p :=
  nonnegative_ite (p 116) (nonnegative4266 p) (nonnegative4265 p)
def d4268 (p : Pattern) : Int := if p 115 then d4267 p else d4229 p
theorem agree4268 (p q : Pattern) (h : Agree support p q) : d4268 p = d4268 q := by
  simp only [d4268, h 115 (by decide), agree4267 p q h, agree4229 p q h]
theorem nonnegative4268 (p : Pattern) : 0 ≤ d4268 p :=
  nonnegative_ite (p 115) (nonnegative4267 p) (nonnegative4229 p)
def d4269 (p : Pattern) : Int := if p 71 then d4268 p else d4232 p
theorem agree4269 (p q : Pattern) (h : Agree support p q) : d4269 p = d4269 q := by
  simp only [d4269, h 71 (by decide), agree4268 p q h, agree4232 p q h]
theorem nonnegative4269 (p : Pattern) : 0 ≤ d4269 p :=
  nonnegative_ite (p 71) (nonnegative4268 p) (nonnegative4232 p)
def d4270 (p : Pattern) : Int := if p 163 then d12 p else d108 p
theorem agree4270 (p q : Pattern) (h : Agree support p q) : d4270 p = d4270 q := by
  simp only [d4270, h 163 (by decide), agree12 p q h, agree108 p q h]
theorem nonnegative4270 (p : Pattern) : 0 ≤ d4270 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative108 p)
def d4271 (p : Pattern) : Int := if p 162 then d4270 p else d4238 p
theorem agree4271 (p q : Pattern) (h : Agree support p q) : d4271 p = d4271 q := by
  simp only [d4271, h 162 (by decide), agree4270 p q h, agree4238 p q h]
theorem nonnegative4271 (p : Pattern) : 0 ≤ d4271 p :=
  nonnegative_ite (p 162) (nonnegative4270 p) (nonnegative4238 p)
def d4272 (p : Pattern) : Int := if p 162 then d12 p else d4270 p
theorem agree4272 (p q : Pattern) (h : Agree support p q) : d4272 p = d4272 q := by
  simp only [d4272, h 162 (by decide), agree12 p q h, agree4270 p q h]
theorem nonnegative4272 (p : Pattern) : 0 ≤ d4272 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4270 p)
def d4273 (p : Pattern) : Int := if p 161 then d4272 p else d4271 p
theorem agree4273 (p q : Pattern) (h : Agree support p q) : d4273 p = d4273 q := by
  simp only [d4273, h 161 (by decide), agree4272 p q h, agree4271 p q h]
theorem nonnegative4273 (p : Pattern) : 0 ≤ d4273 p :=
  nonnegative_ite (p 161) (nonnegative4272 p) (nonnegative4271 p)
def d4274 (p : Pattern) : Int := if p 141 then d4273 p else d4237 p
theorem agree4274 (p q : Pattern) (h : Agree support p q) : d4274 p = d4274 q := by
  simp only [d4274, h 141 (by decide), agree4273 p q h, agree4237 p q h]
theorem nonnegative4274 (p : Pattern) : 0 ≤ d4274 p :=
  nonnegative_ite (p 141) (nonnegative4273 p) (nonnegative4237 p)
def d4275 (p : Pattern) : Int := if p 138 then d4247 p else d4274 p
theorem agree4275 (p q : Pattern) (h : Agree support p q) : d4275 p = d4275 q := by
  simp only [d4275, h 138 (by decide), agree4247 p q h, agree4274 p q h]
theorem nonnegative4275 (p : Pattern) : 0 ≤ d4275 p :=
  nonnegative_ite (p 138) (nonnegative4247 p) (nonnegative4274 p)
def d4276 (p : Pattern) : Int := if p 116 then d4275 p else d4274 p
theorem agree4276 (p q : Pattern) (h : Agree support p q) : d4276 p = d4276 q := by
  simp only [d4276, h 116 (by decide), agree4275 p q h, agree4274 p q h]
theorem nonnegative4276 (p : Pattern) : 0 ≤ d4276 p :=
  nonnegative_ite (p 116) (nonnegative4275 p) (nonnegative4274 p)
def d4277 (p : Pattern) : Int := if p 163 then d41 p else d117 p
theorem agree4277 (p q : Pattern) (h : Agree support p q) : d4277 p = d4277 q := by
  simp only [d4277, h 163 (by decide), agree41 p q h, agree117 p q h]
theorem nonnegative4277 (p : Pattern) : 0 ≤ d4277 p :=
  nonnegative_ite (p 163) (nonnegative41 p) (nonnegative117 p)
def d4278 (p : Pattern) : Int := if p 162 then d4277 p else d104 p
theorem agree4278 (p q : Pattern) (h : Agree support p q) : d4278 p = d4278 q := by
  simp only [d4278, h 162 (by decide), agree4277 p q h, agree104 p q h]
theorem nonnegative4278 (p : Pattern) : 0 ≤ d4278 p :=
  nonnegative_ite (p 162) (nonnegative4277 p) (nonnegative104 p)
def d4279 (p : Pattern) : Int := if p 161 then d4242 p else d4278 p
theorem agree4279 (p q : Pattern) (h : Agree support p q) : d4279 p = d4279 q := by
  simp only [d4279, h 161 (by decide), agree4242 p q h, agree4278 p q h]
theorem nonnegative4279 (p : Pattern) : 0 ≤ d4279 p :=
  nonnegative_ite (p 161) (nonnegative4242 p) (nonnegative4278 p)
def d4280 (p : Pattern) : Int := if p 162 then d4270 p else d117 p
theorem agree4280 (p q : Pattern) (h : Agree support p q) : d4280 p = d4280 q := by
  simp only [d4280, h 162 (by decide), agree4270 p q h, agree117 p q h]
theorem nonnegative4280 (p : Pattern) : 0 ≤ d4280 p :=
  nonnegative_ite (p 162) (nonnegative4270 p) (nonnegative117 p)
def d4281 (p : Pattern) : Int := if p 163 then d12 p else d121 p
theorem agree4281 (p q : Pattern) (h : Agree support p q) : d4281 p = d4281 q := by
  simp only [d4281, h 163 (by decide), agree12 p q h, agree121 p q h]
theorem nonnegative4281 (p : Pattern) : 0 ≤ d4281 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative121 p)
def d4282 (p : Pattern) : Int := if p 162 then d12 p else d4281 p
theorem agree4282 (p q : Pattern) (h : Agree support p q) : d4282 p = d4282 q := by
  simp only [d4282, h 162 (by decide), agree12 p q h, agree4281 p q h]
theorem nonnegative4282 (p : Pattern) : 0 ≤ d4282 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4281 p)
def d4283 (p : Pattern) : Int := if p 161 then d4282 p else d4280 p
theorem agree4283 (p q : Pattern) (h : Agree support p q) : d4283 p = d4283 q := by
  simp only [d4283, h 161 (by decide), agree4282 p q h, agree4280 p q h]
theorem nonnegative4283 (p : Pattern) : 0 ≤ d4283 p :=
  nonnegative_ite (p 161) (nonnegative4282 p) (nonnegative4280 p)
def d4284 (p : Pattern) : Int := if p 141 then d4283 p else d4279 p
theorem agree4284 (p q : Pattern) (h : Agree support p q) : d4284 p = d4284 q := by
  simp only [d4284, h 141 (by decide), agree4283 p q h, agree4279 p q h]
theorem nonnegative4284 (p : Pattern) : 0 ≤ d4284 p :=
  nonnegative_ite (p 141) (nonnegative4283 p) (nonnegative4279 p)
def d4285 (p : Pattern) : Int := if p 138 then d4284 p else d4274 p
theorem agree4285 (p q : Pattern) (h : Agree support p q) : d4285 p = d4285 q := by
  simp only [d4285, h 138 (by decide), agree4284 p q h, agree4274 p q h]
theorem nonnegative4285 (p : Pattern) : 0 ≤ d4285 p :=
  nonnegative_ite (p 138) (nonnegative4284 p) (nonnegative4274 p)
def d4286 (p : Pattern) : Int := if p 163 then d25 p else d117 p
theorem agree4286 (p q : Pattern) (h : Agree support p q) : d4286 p = d4286 q := by
  simp only [d4286, h 163 (by decide), agree25 p q h, agree117 p q h]
theorem nonnegative4286 (p : Pattern) : 0 ≤ d4286 p :=
  nonnegative_ite (p 163) (nonnegative25 p) (nonnegative117 p)
def d4287 (p : Pattern) : Int := if p 162 then d4286 p else d104 p
theorem agree4287 (p q : Pattern) (h : Agree support p q) : d4287 p = d4287 q := by
  simp only [d4287, h 162 (by decide), agree4286 p q h, agree104 p q h]
theorem nonnegative4287 (p : Pattern) : 0 ≤ d4287 p :=
  nonnegative_ite (p 162) (nonnegative4286 p) (nonnegative104 p)
def d4288 (p : Pattern) : Int := if p 163 then d25 p else d108 p
theorem agree4288 (p q : Pattern) (h : Agree support p q) : d4288 p = d4288 q := by
  simp only [d4288, h 163 (by decide), agree25 p q h, agree108 p q h]
theorem nonnegative4288 (p : Pattern) : 0 ≤ d4288 p :=
  nonnegative_ite (p 163) (nonnegative25 p) (nonnegative108 p)
def d4289 (p : Pattern) : Int := if p 162 then d12 p else d4288 p
theorem agree4289 (p q : Pattern) (h : Agree support p q) : d4289 p = d4289 q := by
  simp only [d4289, h 162 (by decide), agree12 p q h, agree4288 p q h]
theorem nonnegative4289 (p : Pattern) : 0 ≤ d4289 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4288 p)
def d4290 (p : Pattern) : Int := if p 161 then d4289 p else d4287 p
theorem agree4290 (p q : Pattern) (h : Agree support p q) : d4290 p = d4290 q := by
  simp only [d4290, h 161 (by decide), agree4289 p q h, agree4287 p q h]
theorem nonnegative4290 (p : Pattern) : 0 ≤ d4290 p :=
  nonnegative_ite (p 161) (nonnegative4289 p) (nonnegative4287 p)
def d4291 (p : Pattern) : Int := if p 141 then d4283 p else d4290 p
theorem agree4291 (p q : Pattern) (h : Agree support p q) : d4291 p = d4291 q := by
  simp only [d4291, h 141 (by decide), agree4283 p q h, agree4290 p q h]
theorem nonnegative4291 (p : Pattern) : 0 ≤ d4291 p :=
  nonnegative_ite (p 141) (nonnegative4283 p) (nonnegative4290 p)
def d4292 (p : Pattern) : Int := if p 138 then d12 p else d4291 p
theorem agree4292 (p q : Pattern) (h : Agree support p q) : d4292 p = d4292 q := by
  simp only [d4292, h 138 (by decide), agree12 p q h, agree4291 p q h]
theorem nonnegative4292 (p : Pattern) : 0 ≤ d4292 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4291 p)
def d4293 (p : Pattern) : Int := if p 116 then d4292 p else d4285 p
theorem agree4293 (p q : Pattern) (h : Agree support p q) : d4293 p = d4293 q := by
  simp only [d4293, h 116 (by decide), agree4292 p q h, agree4285 p q h]
theorem nonnegative4293 (p : Pattern) : 0 ≤ d4293 p :=
  nonnegative_ite (p 116) (nonnegative4292 p) (nonnegative4285 p)
def d4294 (p : Pattern) : Int := if p 115 then d4293 p else d4276 p
theorem agree4294 (p q : Pattern) (h : Agree support p q) : d4294 p = d4294 q := by
  simp only [d4294, h 115 (by decide), agree4293 p q h, agree4276 p q h]
theorem nonnegative4294 (p : Pattern) : 0 ≤ d4294 p :=
  nonnegative_ite (p 115) (nonnegative4293 p) (nonnegative4276 p)
def d4295 (p : Pattern) : Int := if p 71 then d4294 p else d4232 p
theorem agree4295 (p q : Pattern) (h : Agree support p q) : d4295 p = d4295 q := by
  simp only [d4295, h 71 (by decide), agree4294 p q h, agree4232 p q h]
theorem nonnegative4295 (p : Pattern) : 0 ≤ d4295 p :=
  nonnegative_ite (p 71) (nonnegative4294 p) (nonnegative4232 p)
def d4296 (p : Pattern) : Int := if p 49 then d4295 p else d4269 p
theorem agree4296 (p q : Pattern) (h : Agree support p q) : d4296 p = d4296 q := by
  simp only [d4296, h 49 (by decide), agree4295 p q h, agree4269 p q h]
theorem nonnegative4296 (p : Pattern) : 0 ≤ d4296 p :=
  nonnegative_ite (p 49) (nonnegative4295 p) (nonnegative4269 p)
def d4297 (p : Pattern) : Int := if p 48 then d4296 p else d4254 p
theorem agree4297 (p q : Pattern) (h : Agree support p q) : d4297 p = d4297 q := by
  simp only [d4297, h 48 (by decide), agree4296 p q h, agree4254 p q h]
theorem nonnegative4297 (p : Pattern) : 0 ≤ d4297 p :=
  nonnegative_ite (p 48) (nonnegative4296 p) (nonnegative4254 p)
def d4298 (p : Pattern) : Int := if p 161 then d1 p else d0 p
theorem agree4298 (p q : Pattern) (h : Agree support p q) : d4298 p = d4298 q := by
  simp only [d4298, h 161 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4298 (p : Pattern) : 0 ≤ d4298 p :=
  nonnegative_ite (p 161) (nonnegative1 p) (nonnegative0 p)
def d4299 (p : Pattern) : Int := if p 161 then d0 p else d1 p
theorem agree4299 (p q : Pattern) (h : Agree support p q) : d4299 p = d4299 q := by
  simp only [d4299, h 161 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4299 (p : Pattern) : 0 ≤ d4299 p :=
  nonnegative_ite (p 161) (nonnegative0 p) (nonnegative1 p)
def d4300 (p : Pattern) : Int := if p 138 then d0 p else d4299 p
theorem agree4300 (p q : Pattern) (h : Agree support p q) : d4300 p = d4300 q := by
  simp only [d4300, h 138 (by decide), agree0 p q h, agree4299 p q h]
theorem nonnegative4300 (p : Pattern) : 0 ≤ d4300 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative4299 p)
def d4301 (p : Pattern) : Int := if p 160 then d0 p else d4299 p
theorem agree4301 (p q : Pattern) (h : Agree support p q) : d4301 p = d4301 q := by
  simp only [d4301, h 160 (by decide), agree0 p q h, agree4299 p q h]
theorem nonnegative4301 (p : Pattern) : 0 ≤ d4301 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative4299 p)
def d4302 (p : Pattern) : Int := if p 138 then d0 p else d4301 p
theorem agree4302 (p q : Pattern) (h : Agree support p q) : d4302 p = d4302 q := by
  simp only [d4302, h 138 (by decide), agree0 p q h, agree4301 p q h]
theorem nonnegative4302 (p : Pattern) : 0 ≤ d4302 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative4301 p)
def d4303 (p : Pattern) : Int := if p 141 then d0 p else d4148 p
theorem agree4303 (p q : Pattern) (h : Agree support p q) : d4303 p = d4303 q := by
  simp only [d4303, h 141 (by decide), agree0 p q h, agree4148 p q h]
theorem nonnegative4303 (p : Pattern) : 0 ≤ d4303 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative4148 p)
def d4304 (p : Pattern) : Int := if p 141 then d0 p else d4147 p
theorem agree4304 (p q : Pattern) (h : Agree support p q) : d4304 p = d4304 q := by
  simp only [d4304, h 141 (by decide), agree0 p q h, agree4147 p q h]
theorem nonnegative4304 (p : Pattern) : 0 ≤ d4304 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative4147 p)
def d4305 (p : Pattern) : Int := if p 162 then d26 p else d16 p
theorem agree4305 (p q : Pattern) (h : Agree support p q) : d4305 p = d4305 q := by
  simp only [d4305, h 162 (by decide), agree26 p q h, agree16 p q h]
theorem nonnegative4305 (p : Pattern) : 0 ≤ d4305 p :=
  nonnegative_ite (p 162) (nonnegative26 p) (nonnegative16 p)
def d4306 (p : Pattern) : Int := if p 161 then d4305 p else d16 p
theorem agree4306 (p q : Pattern) (h : Agree support p q) : d4306 p = d4306 q := by
  simp only [d4306, h 161 (by decide), agree4305 p q h, agree16 p q h]
theorem nonnegative4306 (p : Pattern) : 0 ≤ d4306 p :=
  nonnegative_ite (p 161) (nonnegative4305 p) (nonnegative16 p)
def d4307 (p : Pattern) : Int := if p 162 then d42 p else d33 p
theorem agree4307 (p q : Pattern) (h : Agree support p q) : d4307 p = d4307 q := by
  simp only [d4307, h 162 (by decide), agree42 p q h, agree33 p q h]
theorem nonnegative4307 (p : Pattern) : 0 ≤ d4307 p :=
  nonnegative_ite (p 162) (nonnegative42 p) (nonnegative33 p)
def d4308 (p : Pattern) : Int := if p 162 then d48 p else d46 p
theorem agree4308 (p q : Pattern) (h : Agree support p q) : d4308 p = d4308 q := by
  simp only [d4308, h 162 (by decide), agree48 p q h, agree46 p q h]
theorem nonnegative4308 (p : Pattern) : 0 ≤ d4308 p :=
  nonnegative_ite (p 162) (nonnegative48 p) (nonnegative46 p)
def d4309 (p : Pattern) : Int := if p 161 then d4308 p else d4307 p
theorem agree4309 (p q : Pattern) (h : Agree support p q) : d4309 p = d4309 q := by
  simp only [d4309, h 161 (by decide), agree4308 p q h, agree4307 p q h]
theorem nonnegative4309 (p : Pattern) : 0 ≤ d4309 p :=
  nonnegative_ite (p 161) (nonnegative4308 p) (nonnegative4307 p)
def d4310 (p : Pattern) : Int := if p 160 then d4309 p else d4306 p
theorem agree4310 (p q : Pattern) (h : Agree support p q) : d4310 p = d4310 q := by
  simp only [d4310, h 160 (by decide), agree4309 p q h, agree4306 p q h]
theorem nonnegative4310 (p : Pattern) : 0 ≤ d4310 p :=
  nonnegative_ite (p 160) (nonnegative4309 p) (nonnegative4306 p)
def d4311 (p : Pattern) : Int := if p 162 then d53 p else d16 p
theorem agree4311 (p q : Pattern) (h : Agree support p q) : d4311 p = d4311 q := by
  simp only [d4311, h 162 (by decide), agree53 p q h, agree16 p q h]
theorem nonnegative4311 (p : Pattern) : 0 ≤ d4311 p :=
  nonnegative_ite (p 162) (nonnegative53 p) (nonnegative16 p)
def d4312 (p : Pattern) : Int := if p 162 then d62 p else d53 p
theorem agree4312 (p q : Pattern) (h : Agree support p q) : d4312 p = d4312 q := by
  simp only [d4312, h 162 (by decide), agree62 p q h, agree53 p q h]
theorem nonnegative4312 (p : Pattern) : 0 ≤ d4312 p :=
  nonnegative_ite (p 162) (nonnegative62 p) (nonnegative53 p)
def d4313 (p : Pattern) : Int := if p 161 then d4312 p else d4311 p
theorem agree4313 (p q : Pattern) (h : Agree support p q) : d4313 p = d4313 q := by
  simp only [d4313, h 161 (by decide), agree4312 p q h, agree4311 p q h]
theorem nonnegative4313 (p : Pattern) : 0 ≤ d4313 p :=
  nonnegative_ite (p 161) (nonnegative4312 p) (nonnegative4311 p)
def d4314 (p : Pattern) : Int := if p 162 then d66 p else d53 p
theorem agree4314 (p q : Pattern) (h : Agree support p q) : d4314 p = d4314 q := by
  simp only [d4314, h 162 (by decide), agree66 p q h, agree53 p q h]
theorem nonnegative4314 (p : Pattern) : 0 ≤ d4314 p :=
  nonnegative_ite (p 162) (nonnegative66 p) (nonnegative53 p)
def d4315 (p : Pattern) : Int := if p 162 then d72 p else d66 p
theorem agree4315 (p q : Pattern) (h : Agree support p q) : d4315 p = d4315 q := by
  simp only [d4315, h 162 (by decide), agree72 p q h, agree66 p q h]
theorem nonnegative4315 (p : Pattern) : 0 ≤ d4315 p :=
  nonnegative_ite (p 162) (nonnegative72 p) (nonnegative66 p)
def d4316 (p : Pattern) : Int := if p 161 then d4315 p else d4314 p
theorem agree4316 (p q : Pattern) (h : Agree support p q) : d4316 p = d4316 q := by
  simp only [d4316, h 161 (by decide), agree4315 p q h, agree4314 p q h]
theorem nonnegative4316 (p : Pattern) : 0 ≤ d4316 p :=
  nonnegative_ite (p 161) (nonnegative4315 p) (nonnegative4314 p)
def d4317 (p : Pattern) : Int := if p 160 then d4316 p else d4313 p
theorem agree4317 (p q : Pattern) (h : Agree support p q) : d4317 p = d4317 q := by
  simp only [d4317, h 160 (by decide), agree4316 p q h, agree4313 p q h]
theorem nonnegative4317 (p : Pattern) : 0 ≤ d4317 p :=
  nonnegative_ite (p 160) (nonnegative4316 p) (nonnegative4313 p)
def d4318 (p : Pattern) : Int := if p 141 then d4317 p else d4310 p
theorem agree4318 (p q : Pattern) (h : Agree support p q) : d4318 p = d4318 q := by
  simp only [d4318, h 141 (by decide), agree4317 p q h, agree4310 p q h]
theorem nonnegative4318 (p : Pattern) : 0 ≤ d4318 p :=
  nonnegative_ite (p 141) (nonnegative4317 p) (nonnegative4310 p)
def d4319 (p : Pattern) : Int := if p 161 then d12 p else d4312 p
theorem agree4319 (p q : Pattern) (h : Agree support p q) : d4319 p = d4319 q := by
  simp only [d4319, h 161 (by decide), agree12 p q h, agree4312 p q h]
theorem nonnegative4319 (p : Pattern) : 0 ≤ d4319 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4312 p)
end NetHack.Sokoban22Refined85
