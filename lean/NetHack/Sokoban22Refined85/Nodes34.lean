/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes33
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4080 (p : Pattern) : Int := if p 116 then d4079 p else d4078 p
theorem agree4080 (p q : Pattern) (h : Agree support p q) : d4080 p = d4080 q := by
  simp only [d4080, h 116 (by decide), agree4079 p q h, agree4078 p q h]
theorem nonnegative4080 (p : Pattern) : 0 ≤ d4080 p :=
  nonnegative_ite (p 116) (nonnegative4079 p) (nonnegative4078 p)
def d4081 (p : Pattern) : Int := if p 138 then d12 p else d86 p
theorem agree4081 (p q : Pattern) (h : Agree support p q) : d4081 p = d4081 q := by
  simp only [d4081, h 138 (by decide), agree12 p q h, agree86 p q h]
theorem nonnegative4081 (p : Pattern) : 0 ≤ d4081 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative86 p)
def d4082 (p : Pattern) : Int := if p 116 then d4081 p else d4078 p
theorem agree4082 (p q : Pattern) (h : Agree support p q) : d4082 p = d4082 q := by
  simp only [d4082, h 116 (by decide), agree4081 p q h, agree4078 p q h]
theorem nonnegative4082 (p : Pattern) : 0 ≤ d4082 p :=
  nonnegative_ite (p 116) (nonnegative4081 p) (nonnegative4078 p)
def d4083 (p : Pattern) : Int := if p 115 then d4082 p else d4080 p
theorem agree4083 (p q : Pattern) (h : Agree support p q) : d4083 p = d4083 q := by
  simp only [d4083, h 115 (by decide), agree4082 p q h, agree4080 p q h]
theorem nonnegative4083 (p : Pattern) : 0 ≤ d4083 p :=
  nonnegative_ite (p 115) (nonnegative4082 p) (nonnegative4080 p)
def d4084 (p : Pattern) : Int := if p 138 then d156 p else d146 p
theorem agree4084 (p q : Pattern) (h : Agree support p q) : d4084 p = d4084 q := by
  simp only [d4084, h 138 (by decide), agree156 p q h, agree146 p q h]
theorem nonnegative4084 (p : Pattern) : 0 ≤ d4084 p :=
  nonnegative_ite (p 138) (nonnegative156 p) (nonnegative146 p)
def d4085 (p : Pattern) : Int := if p 138 then d12 p else d156 p
theorem agree4085 (p q : Pattern) (h : Agree support p q) : d4085 p = d4085 q := by
  simp only [d4085, h 138 (by decide), agree12 p q h, agree156 p q h]
theorem nonnegative4085 (p : Pattern) : 0 ≤ d4085 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative156 p)
def d4086 (p : Pattern) : Int := if p 116 then d4085 p else d4084 p
theorem agree4086 (p q : Pattern) (h : Agree support p q) : d4086 p = d4086 q := by
  simp only [d4086, h 116 (by decide), agree4085 p q h, agree4084 p q h]
theorem nonnegative4086 (p : Pattern) : 0 ≤ d4086 p :=
  nonnegative_ite (p 116) (nonnegative4085 p) (nonnegative4084 p)
def d4087 (p : Pattern) : Int := if p 71 then d4086 p else d4083 p
theorem agree4087 (p q : Pattern) (h : Agree support p q) : d4087 p = d4087 q := by
  simp only [d4087, h 71 (by decide), agree4086 p q h, agree4083 p q h]
theorem nonnegative4087 (p : Pattern) : 0 ≤ d4087 p :=
  nonnegative_ite (p 71) (nonnegative4086 p) (nonnegative4083 p)
def d4088 (p : Pattern) : Int := if p 49 then d4087 p else d4083 p
theorem agree4088 (p q : Pattern) (h : Agree support p q) : d4088 p = d4088 q := by
  simp only [d4088, h 49 (by decide), agree4087 p q h, agree4083 p q h]
theorem nonnegative4088 (p : Pattern) : 0 ≤ d4088 p :=
  nonnegative_ite (p 49) (nonnegative4087 p) (nonnegative4083 p)
def d4089 (p : Pattern) : Int := if p 138 then d221 p else d219 p
theorem agree4089 (p q : Pattern) (h : Agree support p q) : d4089 p = d4089 q := by
  simp only [d4089, h 138 (by decide), agree221 p q h, agree219 p q h]
theorem nonnegative4089 (p : Pattern) : 0 ≤ d4089 p :=
  nonnegative_ite (p 138) (nonnegative221 p) (nonnegative219 p)
def d4090 (p : Pattern) : Int := if p 138 then d12 p else d221 p
theorem agree4090 (p q : Pattern) (h : Agree support p q) : d4090 p = d4090 q := by
  simp only [d4090, h 138 (by decide), agree12 p q h, agree221 p q h]
theorem nonnegative4090 (p : Pattern) : 0 ≤ d4090 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative221 p)
def d4091 (p : Pattern) : Int := if p 116 then d4090 p else d4089 p
theorem agree4091 (p q : Pattern) (h : Agree support p q) : d4091 p = d4091 q := by
  simp only [d4091, h 116 (by decide), agree4090 p q h, agree4089 p q h]
theorem nonnegative4091 (p : Pattern) : 0 ≤ d4091 p :=
  nonnegative_ite (p 116) (nonnegative4090 p) (nonnegative4089 p)
def d4092 (p : Pattern) : Int := if p 138 then d304 p else d289 p
theorem agree4092 (p q : Pattern) (h : Agree support p q) : d4092 p = d4092 q := by
  simp only [d4092, h 138 (by decide), agree304 p q h, agree289 p q h]
theorem nonnegative4092 (p : Pattern) : 0 ≤ d4092 p :=
  nonnegative_ite (p 138) (nonnegative304 p) (nonnegative289 p)
def d4093 (p : Pattern) : Int := if p 138 then d12 p else d304 p
theorem agree4093 (p q : Pattern) (h : Agree support p q) : d4093 p = d4093 q := by
  simp only [d4093, h 138 (by decide), agree12 p q h, agree304 p q h]
theorem nonnegative4093 (p : Pattern) : 0 ≤ d4093 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative304 p)
def d4094 (p : Pattern) : Int := if p 116 then d4093 p else d4092 p
theorem agree4094 (p q : Pattern) (h : Agree support p q) : d4094 p = d4094 q := by
  simp only [d4094, h 116 (by decide), agree4093 p q h, agree4092 p q h]
theorem nonnegative4094 (p : Pattern) : 0 ≤ d4094 p :=
  nonnegative_ite (p 116) (nonnegative4093 p) (nonnegative4092 p)
def d4095 (p : Pattern) : Int := if p 115 then d4094 p else d4091 p
theorem agree4095 (p q : Pattern) (h : Agree support p q) : d4095 p = d4095 q := by
  simp only [d4095, h 115 (by decide), agree4094 p q h, agree4091 p q h]
theorem nonnegative4095 (p : Pattern) : 0 ≤ d4095 p :=
  nonnegative_ite (p 115) (nonnegative4094 p) (nonnegative4091 p)
def d4096 (p : Pattern) : Int := if p 71 then d4095 p else d4083 p
theorem agree4096 (p q : Pattern) (h : Agree support p q) : d4096 p = d4096 q := by
  simp only [d4096, h 71 (by decide), agree4095 p q h, agree4083 p q h]
theorem nonnegative4096 (p : Pattern) : 0 ≤ d4096 p :=
  nonnegative_ite (p 71) (nonnegative4095 p) (nonnegative4083 p)
def d4097 (p : Pattern) : Int := if p 49 then d4096 p else d4083 p
theorem agree4097 (p q : Pattern) (h : Agree support p q) : d4097 p = d4097 q := by
  simp only [d4097, h 49 (by decide), agree4096 p q h, agree4083 p q h]
theorem nonnegative4097 (p : Pattern) : 0 ≤ d4097 p :=
  nonnegative_ite (p 49) (nonnegative4096 p) (nonnegative4083 p)
def d4098 (p : Pattern) : Int := if p 48 then d4097 p else d4088 p
theorem agree4098 (p q : Pattern) (h : Agree support p q) : d4098 p = d4098 q := by
  simp only [d4098, h 48 (by decide), agree4097 p q h, agree4088 p q h]
theorem nonnegative4098 (p : Pattern) : 0 ≤ d4098 p :=
  nonnegative_ite (p 48) (nonnegative4097 p) (nonnegative4088 p)
def d4099 (p : Pattern) : Int := if p 71 then d208 p else d100 p
theorem agree4099 (p q : Pattern) (h : Agree support p q) : d4099 p = d4099 q := by
  simp only [d4099, h 71 (by decide), agree208 p q h, agree100 p q h]
theorem nonnegative4099 (p : Pattern) : 0 ≤ d4099 p :=
  nonnegative_ite (p 71) (nonnegative208 p) (nonnegative100 p)
def d4100 (p : Pattern) : Int := if p 71 then d263 p else d100 p
theorem agree4100 (p q : Pattern) (h : Agree support p q) : d4100 p = d4100 q := by
  simp only [d4100, h 71 (by decide), agree263 p q h, agree100 p q h]
theorem nonnegative4100 (p : Pattern) : 0 ≤ d4100 p :=
  nonnegative_ite (p 71) (nonnegative263 p) (nonnegative100 p)
def d4101 (p : Pattern) : Int := if p 49 then d4100 p else d4099 p
theorem agree4101 (p q : Pattern) (h : Agree support p q) : d4101 p = d4101 q := by
  simp only [d4101, h 49 (by decide), agree4100 p q h, agree4099 p q h]
theorem nonnegative4101 (p : Pattern) : 0 ≤ d4101 p :=
  nonnegative_ite (p 49) (nonnegative4100 p) (nonnegative4099 p)
def d4102 (p : Pattern) : Int := if p 48 then d4101 p else d4061 p
theorem agree4102 (p q : Pattern) (h : Agree support p q) : d4102 p = d4102 q := by
  simp only [d4102, h 48 (by decide), agree4101 p q h, agree4061 p q h]
theorem nonnegative4102 (p : Pattern) : 0 ≤ d4102 p :=
  nonnegative_ite (p 48) (nonnegative4101 p) (nonnegative4061 p)
def d4103 (p : Pattern) : Int := if p 115 then d4066 p else d0 p
theorem agree4103 (p q : Pattern) (h : Agree support p q) : d4103 p = d4103 q := by
  simp only [d4103, h 115 (by decide), agree4066 p q h, agree0 p q h]
theorem nonnegative4103 (p : Pattern) : 0 ≤ d4103 p :=
  nonnegative_ite (p 115) (nonnegative4066 p) (nonnegative0 p)
def d4104 (p : Pattern) : Int := if p 71 then d163 p else d97 p
theorem agree4104 (p q : Pattern) (h : Agree support p q) : d4104 p = d4104 q := by
  simp only [d4104, h 71 (by decide), agree163 p q h, agree97 p q h]
theorem nonnegative4104 (p : Pattern) : 0 ≤ d4104 p :=
  nonnegative_ite (p 71) (nonnegative163 p) (nonnegative97 p)
def d4105 (p : Pattern) : Int := if p 49 then d4104 p else d97 p
theorem agree4105 (p q : Pattern) (h : Agree support p q) : d4105 p = d4105 q := by
  simp only [d4105, h 49 (by decide), agree4104 p q h, agree97 p q h]
theorem nonnegative4105 (p : Pattern) : 0 ≤ d4105 p :=
  nonnegative_ite (p 49) (nonnegative4104 p) (nonnegative97 p)
def d4106 (p : Pattern) : Int := if p 71 then d224 p else d97 p
theorem agree4106 (p q : Pattern) (h : Agree support p q) : d4106 p = d4106 q := by
  simp only [d4106, h 71 (by decide), agree224 p q h, agree97 p q h]
theorem nonnegative4106 (p : Pattern) : 0 ≤ d4106 p :=
  nonnegative_ite (p 71) (nonnegative224 p) (nonnegative97 p)
def d4107 (p : Pattern) : Int := if p 49 then d4106 p else d97 p
theorem agree4107 (p q : Pattern) (h : Agree support p q) : d4107 p = d4107 q := by
  simp only [d4107, h 49 (by decide), agree4106 p q h, agree97 p q h]
theorem nonnegative4107 (p : Pattern) : 0 ≤ d4107 p :=
  nonnegative_ite (p 49) (nonnegative4106 p) (nonnegative97 p)
def d4108 (p : Pattern) : Int := if p 48 then d4107 p else d4105 p
theorem agree4108 (p q : Pattern) (h : Agree support p q) : d4108 p = d4108 q := by
  simp only [d4108, h 48 (by decide), agree4107 p q h, agree4105 p q h]
theorem nonnegative4108 (p : Pattern) : 0 ≤ d4108 p :=
  nonnegative_ite (p 48) (nonnegative4107 p) (nonnegative4105 p)
def d4109 (p : Pattern) : Int := if p 49 then d309 p else d101 p
theorem agree4109 (p q : Pattern) (h : Agree support p q) : d4109 p = d4109 q := by
  simp only [d4109, h 49 (by decide), agree309 p q h, agree101 p q h]
theorem nonnegative4109 (p : Pattern) : 0 ≤ d4109 p :=
  nonnegative_ite (p 49) (nonnegative309 p) (nonnegative101 p)
def d4110 (p : Pattern) : Int := if p 48 then d4109 p else d4054 p
theorem agree4110 (p q : Pattern) (h : Agree support p q) : d4110 p = d4110 q := by
  simp only [d4110, h 48 (by decide), agree4109 p q h, agree4054 p q h]
theorem nonnegative4110 (p : Pattern) : 0 ≤ d4110 p :=
  nonnegative_ite (p 48) (nonnegative4109 p) (nonnegative4054 p)
def d4111 (p : Pattern) : Int := if p 115 then d0 p else d4066 p
theorem agree4111 (p q : Pattern) (h : Agree support p q) : d4111 p = d4111 q := by
  simp only [d4111, h 115 (by decide), agree0 p q h, agree4066 p q h]
theorem nonnegative4111 (p : Pattern) : 0 ≤ d4111 p :=
  nonnegative_ite (p 115) (nonnegative0 p) (nonnegative4066 p)
def d4112 (p : Pattern) : Int := if p 115 then d0 p else d4068 p
theorem agree4112 (p q : Pattern) (h : Agree support p q) : d4112 p = d4112 q := by
  simp only [d4112, h 115 (by decide), agree0 p q h, agree4068 p q h]
theorem nonnegative4112 (p : Pattern) : 0 ≤ d4112 p :=
  nonnegative_ite (p 115) (nonnegative0 p) (nonnegative4068 p)
def d4113 (p : Pattern) : Int := if p 116 then d0 p else d4068 p
theorem agree4113 (p q : Pattern) (h : Agree support p q) : d4113 p = d4113 q := by
  simp only [d4113, h 116 (by decide), agree0 p q h, agree4068 p q h]
theorem nonnegative4113 (p : Pattern) : 0 ≤ d4113 p :=
  nonnegative_ite (p 116) (nonnegative0 p) (nonnegative4068 p)
def d4114 (p : Pattern) : Int := if p 115 then d0 p else d4113 p
theorem agree4114 (p q : Pattern) (h : Agree support p q) : d4114 p = d4114 q := by
  simp only [d4114, h 115 (by decide), agree0 p q h, agree4113 p q h]
theorem nonnegative4114 (p : Pattern) : 0 ≤ d4114 p :=
  nonnegative_ite (p 115) (nonnegative0 p) (nonnegative4113 p)
def d4115 (p : Pattern) : Int := if p 116 then d0 p else d4067 p
theorem agree4115 (p q : Pattern) (h : Agree support p q) : d4115 p = d4115 q := by
  simp only [d4115, h 116 (by decide), agree0 p q h, agree4067 p q h]
theorem nonnegative4115 (p : Pattern) : 0 ≤ d4115 p :=
  nonnegative_ite (p 116) (nonnegative0 p) (nonnegative4067 p)
def d4116 (p : Pattern) : Int := if p 160 then d1 p else d0 p
theorem agree4116 (p q : Pattern) (h : Agree support p q) : d4116 p = d4116 q := by
  simp only [d4116, h 160 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4116 (p : Pattern) : 0 ≤ d4116 p :=
  nonnegative_ite (p 160) (nonnegative1 p) (nonnegative0 p)
def d4117 (p : Pattern) : Int := if p 160 then d0 p else d1 p
theorem agree4117 (p q : Pattern) (h : Agree support p q) : d4117 p = d4117 q := by
  simp only [d4117, h 160 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4117 (p : Pattern) : 0 ≤ d4117 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative1 p)
def d4118 (p : Pattern) : Int := if p 138 then d4117 p else d0 p
theorem agree4118 (p q : Pattern) (h : Agree support p q) : d4118 p = d4118 q := by
  simp only [d4118, h 138 (by decide), agree4117 p q h, agree0 p q h]
theorem nonnegative4118 (p : Pattern) : 0 ≤ d4118 p :=
  nonnegative_ite (p 138) (nonnegative4117 p) (nonnegative0 p)
def d4119 (p : Pattern) : Int := if p 116 then d0 p else d4118 p
theorem agree4119 (p q : Pattern) (h : Agree support p q) : d4119 p = d4119 q := by
  simp only [d4119, h 116 (by decide), agree0 p q h, agree4118 p q h]
theorem nonnegative4119 (p : Pattern) : 0 ≤ d4119 p :=
  nonnegative_ite (p 116) (nonnegative0 p) (nonnegative4118 p)
def d4120 (p : Pattern) : Int := if p 141 then d75 p else d51 p
theorem agree4120 (p q : Pattern) (h : Agree support p q) : d4120 p = d4120 q := by
  simp only [d4120, h 141 (by decide), agree75 p q h, agree51 p q h]
theorem nonnegative4120 (p : Pattern) : 0 ≤ d4120 p :=
  nonnegative_ite (p 141) (nonnegative75 p) (nonnegative51 p)
def d4121 (p : Pattern) : Int := if p 141 then d541 p else d530 p
theorem agree4121 (p q : Pattern) (h : Agree support p q) : d4121 p = d4121 q := by
  simp only [d4121, h 141 (by decide), agree541 p q h, agree530 p q h]
theorem nonnegative4121 (p : Pattern) : 0 ≤ d4121 p :=
  nonnegative_ite (p 141) (nonnegative541 p) (nonnegative530 p)
def d4122 (p : Pattern) : Int := if p 116 then d4121 p else d4120 p
theorem agree4122 (p q : Pattern) (h : Agree support p q) : d4122 p = d4122 q := by
  simp only [d4122, h 116 (by decide), agree4121 p q h, agree4120 p q h]
theorem nonnegative4122 (p : Pattern) : 0 ≤ d4122 p :=
  nonnegative_ite (p 116) (nonnegative4121 p) (nonnegative4120 p)
def d4123 (p : Pattern) : Int := if p 141 then d145 p else d130 p
theorem agree4123 (p q : Pattern) (h : Agree support p q) : d4123 p = d4123 q := by
  simp only [d4123, h 141 (by decide), agree145 p q h, agree130 p q h]
theorem nonnegative4123 (p : Pattern) : 0 ≤ d4123 p :=
  nonnegative_ite (p 141) (nonnegative145 p) (nonnegative130 p)
def d4124 (p : Pattern) : Int := if p 141 then d577 p else d568 p
theorem agree4124 (p q : Pattern) (h : Agree support p q) : d4124 p = d4124 q := by
  simp only [d4124, h 141 (by decide), agree577 p q h, agree568 p q h]
theorem nonnegative4124 (p : Pattern) : 0 ≤ d4124 p :=
  nonnegative_ite (p 141) (nonnegative577 p) (nonnegative568 p)
def d4125 (p : Pattern) : Int := if p 116 then d4124 p else d4123 p
theorem agree4125 (p q : Pattern) (h : Agree support p q) : d4125 p = d4125 q := by
  simp only [d4125, h 116 (by decide), agree4124 p q h, agree4123 p q h]
theorem nonnegative4125 (p : Pattern) : 0 ≤ d4125 p :=
  nonnegative_ite (p 116) (nonnegative4124 p) (nonnegative4123 p)
def d4126 (p : Pattern) : Int := if p 71 then d4125 p else d4122 p
theorem agree4126 (p q : Pattern) (h : Agree support p q) : d4126 p = d4126 q := by
  simp only [d4126, h 71 (by decide), agree4125 p q h, agree4122 p q h]
theorem nonnegative4126 (p : Pattern) : 0 ≤ d4126 p :=
  nonnegative_ite (p 71) (nonnegative4125 p) (nonnegative4122 p)
def d4127 (p : Pattern) : Int := if p 49 then d4126 p else d4122 p
theorem agree4127 (p q : Pattern) (h : Agree support p q) : d4127 p = d4127 q := by
  simp only [d4127, h 49 (by decide), agree4126 p q h, agree4122 p q h]
theorem nonnegative4127 (p : Pattern) : 0 ≤ d4127 p :=
  nonnegative_ite (p 49) (nonnegative4126 p) (nonnegative4122 p)
def d4128 (p : Pattern) : Int := if p 141 then d603 p else d595 p
theorem agree4128 (p q : Pattern) (h : Agree support p q) : d4128 p = d4128 q := by
  simp only [d4128, h 141 (by decide), agree603 p q h, agree595 p q h]
theorem nonnegative4128 (p : Pattern) : 0 ≤ d4128 p :=
  nonnegative_ite (p 141) (nonnegative603 p) (nonnegative595 p)
def d4129 (p : Pattern) : Int := if p 116 then d4128 p else d4120 p
theorem agree4129 (p q : Pattern) (h : Agree support p q) : d4129 p = d4129 q := by
  simp only [d4129, h 116 (by decide), agree4128 p q h, agree4120 p q h]
theorem nonnegative4129 (p : Pattern) : 0 ≤ d4129 p :=
  nonnegative_ite (p 116) (nonnegative4128 p) (nonnegative4120 p)
def d4130 (p : Pattern) : Int := if p 115 then d4129 p else d4122 p
theorem agree4130 (p q : Pattern) (h : Agree support p q) : d4130 p = d4130 q := by
  simp only [d4130, h 115 (by decide), agree4129 p q h, agree4122 p q h]
theorem nonnegative4130 (p : Pattern) : 0 ≤ d4130 p :=
  nonnegative_ite (p 115) (nonnegative4129 p) (nonnegative4122 p)
def d4131 (p : Pattern) : Int := if p 71 then d4130 p else d4122 p
theorem agree4131 (p q : Pattern) (h : Agree support p q) : d4131 p = d4131 q := by
  simp only [d4131, h 71 (by decide), agree4130 p q h, agree4122 p q h]
theorem nonnegative4131 (p : Pattern) : 0 ≤ d4131 p :=
  nonnegative_ite (p 71) (nonnegative4130 p) (nonnegative4122 p)
def d4132 (p : Pattern) : Int := if p 141 then d218 p else d130 p
theorem agree4132 (p q : Pattern) (h : Agree support p q) : d4132 p = d4132 q := by
  simp only [d4132, h 141 (by decide), agree218 p q h, agree130 p q h]
theorem nonnegative4132 (p : Pattern) : 0 ≤ d4132 p :=
  nonnegative_ite (p 141) (nonnegative218 p) (nonnegative130 p)
def d4133 (p : Pattern) : Int := if p 141 then d614 p else d568 p
theorem agree4133 (p q : Pattern) (h : Agree support p q) : d4133 p = d4133 q := by
  simp only [d4133, h 141 (by decide), agree614 p q h, agree568 p q h]
theorem nonnegative4133 (p : Pattern) : 0 ≤ d4133 p :=
  nonnegative_ite (p 141) (nonnegative614 p) (nonnegative568 p)
def d4134 (p : Pattern) : Int := if p 116 then d4133 p else d4132 p
theorem agree4134 (p q : Pattern) (h : Agree support p q) : d4134 p = d4134 q := by
  simp only [d4134, h 116 (by decide), agree4133 p q h, agree4132 p q h]
theorem nonnegative4134 (p : Pattern) : 0 ≤ d4134 p :=
  nonnegative_ite (p 116) (nonnegative4133 p) (nonnegative4132 p)
def d4135 (p : Pattern) : Int := if p 141 then d288 p else d280 p
theorem agree4135 (p q : Pattern) (h : Agree support p q) : d4135 p = d4135 q := by
  simp only [d4135, h 141 (by decide), agree288 p q h, agree280 p q h]
theorem nonnegative4135 (p : Pattern) : 0 ≤ d4135 p :=
  nonnegative_ite (p 141) (nonnegative288 p) (nonnegative280 p)
def d4136 (p : Pattern) : Int := if p 141 then d644 p else d630 p
theorem agree4136 (p q : Pattern) (h : Agree support p q) : d4136 p = d4136 q := by
  simp only [d4136, h 141 (by decide), agree644 p q h, agree630 p q h]
theorem nonnegative4136 (p : Pattern) : 0 ≤ d4136 p :=
  nonnegative_ite (p 141) (nonnegative644 p) (nonnegative630 p)
def d4137 (p : Pattern) : Int := if p 116 then d4136 p else d4135 p
theorem agree4137 (p q : Pattern) (h : Agree support p q) : d4137 p = d4137 q := by
  simp only [d4137, h 116 (by decide), agree4136 p q h, agree4135 p q h]
theorem nonnegative4137 (p : Pattern) : 0 ≤ d4137 p :=
  nonnegative_ite (p 116) (nonnegative4136 p) (nonnegative4135 p)
def d4138 (p : Pattern) : Int := if p 115 then d4137 p else d4134 p
theorem agree4138 (p q : Pattern) (h : Agree support p q) : d4138 p = d4138 q := by
  simp only [d4138, h 115 (by decide), agree4137 p q h, agree4134 p q h]
theorem nonnegative4138 (p : Pattern) : 0 ≤ d4138 p :=
  nonnegative_ite (p 115) (nonnegative4137 p) (nonnegative4134 p)
def d4139 (p : Pattern) : Int := if p 71 then d4138 p else d4122 p
theorem agree4139 (p q : Pattern) (h : Agree support p q) : d4139 p = d4139 q := by
  simp only [d4139, h 71 (by decide), agree4138 p q h, agree4122 p q h]
theorem nonnegative4139 (p : Pattern) : 0 ≤ d4139 p :=
  nonnegative_ite (p 71) (nonnegative4138 p) (nonnegative4122 p)
def d4140 (p : Pattern) : Int := if p 49 then d4139 p else d4131 p
theorem agree4140 (p q : Pattern) (h : Agree support p q) : d4140 p = d4140 q := by
  simp only [d4140, h 49 (by decide), agree4139 p q h, agree4131 p q h]
theorem nonnegative4140 (p : Pattern) : 0 ≤ d4140 p :=
  nonnegative_ite (p 49) (nonnegative4139 p) (nonnegative4131 p)
def d4141 (p : Pattern) : Int := if p 48 then d4140 p else d4127 p
theorem agree4141 (p q : Pattern) (h : Agree support p q) : d4141 p = d4141 q := by
  simp only [d4141, h 48 (by decide), agree4140 p q h, agree4127 p q h]
theorem nonnegative4141 (p : Pattern) : 0 ≤ d4141 p :=
  nonnegative_ite (p 48) (nonnegative4140 p) (nonnegative4127 p)
def d4142 (p : Pattern) : Int := if p 71 then d164 p else d98 p
theorem agree4142 (p q : Pattern) (h : Agree support p q) : d4142 p = d4142 q := by
  simp only [d4142, h 71 (by decide), agree164 p q h, agree98 p q h]
theorem nonnegative4142 (p : Pattern) : 0 ≤ d4142 p :=
  nonnegative_ite (p 71) (nonnegative164 p) (nonnegative98 p)
def d4143 (p : Pattern) : Int := if p 49 then d4142 p else d98 p
theorem agree4143 (p q : Pattern) (h : Agree support p q) : d4143 p = d4143 q := by
  simp only [d4143, h 49 (by decide), agree4142 p q h, agree98 p q h]
theorem nonnegative4143 (p : Pattern) : 0 ≤ d4143 p :=
  nonnegative_ite (p 49) (nonnegative4142 p) (nonnegative98 p)
def d4144 (p : Pattern) : Int := if p 71 then d225 p else d98 p
theorem agree4144 (p q : Pattern) (h : Agree support p q) : d4144 p = d4144 q := by
  simp only [d4144, h 71 (by decide), agree225 p q h, agree98 p q h]
theorem nonnegative4144 (p : Pattern) : 0 ≤ d4144 p :=
  nonnegative_ite (p 71) (nonnegative225 p) (nonnegative98 p)
def d4145 (p : Pattern) : Int := if p 49 then d4144 p else d98 p
theorem agree4145 (p q : Pattern) (h : Agree support p q) : d4145 p = d4145 q := by
  simp only [d4145, h 49 (by decide), agree4144 p q h, agree98 p q h]
theorem nonnegative4145 (p : Pattern) : 0 ≤ d4145 p :=
  nonnegative_ite (p 49) (nonnegative4144 p) (nonnegative98 p)
def d4146 (p : Pattern) : Int := if p 48 then d4145 p else d4143 p
theorem agree4146 (p q : Pattern) (h : Agree support p q) : d4146 p = d4146 q := by
  simp only [d4146, h 48 (by decide), agree4145 p q h, agree4143 p q h]
theorem nonnegative4146 (p : Pattern) : 0 ≤ d4146 p :=
  nonnegative_ite (p 48) (nonnegative4145 p) (nonnegative4143 p)
def d4147 (p : Pattern) : Int := if p 163 then d1 p else d0 p
theorem agree4147 (p q : Pattern) (h : Agree support p q) : d4147 p = d4147 q := by
  simp only [d4147, h 163 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4147 (p : Pattern) : 0 ≤ d4147 p :=
  nonnegative_ite (p 163) (nonnegative1 p) (nonnegative0 p)
def d4148 (p : Pattern) : Int := if p 163 then d0 p else d1 p
theorem agree4148 (p q : Pattern) (h : Agree support p q) : d4148 p = d4148 q := by
  simp only [d4148, h 163 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4148 (p : Pattern) : 0 ≤ d4148 p :=
  nonnegative_ite (p 163) (nonnegative0 p) (nonnegative1 p)
def d4149 (p : Pattern) : Int := if p 141 then d4148 p else d0 p
theorem agree4149 (p q : Pattern) (h : Agree support p q) : d4149 p = d4149 q := by
  simp only [d4149, h 141 (by decide), agree4148 p q h, agree0 p q h]
theorem nonnegative4149 (p : Pattern) : 0 ≤ d4149 p :=
  nonnegative_ite (p 141) (nonnegative4148 p) (nonnegative0 p)
def d4150 (p : Pattern) : Int := if p 162 then d20 p else d16 p
theorem agree4150 (p q : Pattern) (h : Agree support p q) : d4150 p = d4150 q := by
  simp only [d4150, h 162 (by decide), agree20 p q h, agree16 p q h]
theorem nonnegative4150 (p : Pattern) : 0 ≤ d4150 p :=
  nonnegative_ite (p 162) (nonnegative20 p) (nonnegative16 p)
def d4151 (p : Pattern) : Int := if p 161 then d1100 p else d4150 p
theorem agree4151 (p q : Pattern) (h : Agree support p q) : d4151 p = d4151 q := by
  simp only [d4151, h 161 (by decide), agree1100 p q h, agree4150 p q h]
theorem nonnegative4151 (p : Pattern) : 0 ≤ d4151 p :=
  nonnegative_ite (p 161) (nonnegative1100 p) (nonnegative4150 p)
def d4152 (p : Pattern) : Int := if p 162 then d43 p else d37 p
theorem agree4152 (p q : Pattern) (h : Agree support p q) : d4152 p = d4152 q := by
  simp only [d4152, h 162 (by decide), agree43 p q h, agree37 p q h]
theorem nonnegative4152 (p : Pattern) : 0 ≤ d4152 p :=
  nonnegative_ite (p 162) (nonnegative43 p) (nonnegative37 p)
def d4153 (p : Pattern) : Int := if p 162 then d12 p else d43 p
theorem agree4153 (p q : Pattern) (h : Agree support p q) : d4153 p = d4153 q := by
  simp only [d4153, h 162 (by decide), agree12 p q h, agree43 p q h]
theorem nonnegative4153 (p : Pattern) : 0 ≤ d4153 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative43 p)
def d4154 (p : Pattern) : Int := if p 161 then d4153 p else d4152 p
theorem agree4154 (p q : Pattern) (h : Agree support p q) : d4154 p = d4154 q := by
  simp only [d4154, h 161 (by decide), agree4153 p q h, agree4152 p q h]
theorem nonnegative4154 (p : Pattern) : 0 ≤ d4154 p :=
  nonnegative_ite (p 161) (nonnegative4153 p) (nonnegative4152 p)
def d4155 (p : Pattern) : Int := if p 160 then d4154 p else d4151 p
theorem agree4155 (p q : Pattern) (h : Agree support p q) : d4155 p = d4155 q := by
  simp only [d4155, h 160 (by decide), agree4154 p q h, agree4151 p q h]
theorem nonnegative4155 (p : Pattern) : 0 ≤ d4155 p :=
  nonnegative_ite (p 160) (nonnegative4154 p) (nonnegative4151 p)
def d4156 (p : Pattern) : Int := if p 162 then d12 p else d78 p
theorem agree4156 (p q : Pattern) (h : Agree support p q) : d4156 p = d4156 q := by
  simp only [d4156, h 162 (by decide), agree12 p q h, agree78 p q h]
theorem nonnegative4156 (p : Pattern) : 0 ≤ d4156 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative78 p)
def d4157 (p : Pattern) : Int := if p 161 then d12 p else d4156 p
theorem agree4157 (p q : Pattern) (h : Agree support p q) : d4157 p = d4157 q := by
  simp only [d4157, h 161 (by decide), agree12 p q h, agree4156 p q h]
theorem nonnegative4157 (p : Pattern) : 0 ≤ d4157 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4156 p)
def d4158 (p : Pattern) : Int := if p 160 then d4157 p else d4151 p
theorem agree4158 (p q : Pattern) (h : Agree support p q) : d4158 p = d4158 q := by
  simp only [d4158, h 160 (by decide), agree4157 p q h, agree4151 p q h]
theorem nonnegative4158 (p : Pattern) : 0 ≤ d4158 p :=
  nonnegative_ite (p 160) (nonnegative4157 p) (nonnegative4151 p)
def d4159 (p : Pattern) : Int := if p 138 then d4158 p else d4155 p
theorem agree4159 (p q : Pattern) (h : Agree support p q) : d4159 p = d4159 q := by
  simp only [d4159, h 138 (by decide), agree4158 p q h, agree4155 p q h]
theorem nonnegative4159 (p : Pattern) : 0 ≤ d4159 p :=
  nonnegative_ite (p 138) (nonnegative4158 p) (nonnegative4155 p)
def d4160 (p : Pattern) : Int := if p 162 then d12 p else d62 p
theorem agree4160 (p q : Pattern) (h : Agree support p q) : d4160 p = d4160 q := by
  simp only [d4160, h 162 (by decide), agree12 p q h, agree62 p q h]
theorem nonnegative4160 (p : Pattern) : 0 ≤ d4160 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative62 p)
def d4161 (p : Pattern) : Int := if p 161 then d12 p else d4160 p
theorem agree4161 (p q : Pattern) (h : Agree support p q) : d4161 p = d4161 q := by
  simp only [d4161, h 161 (by decide), agree12 p q h, agree4160 p q h]
theorem nonnegative4161 (p : Pattern) : 0 ≤ d4161 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4160 p)
def d4162 (p : Pattern) : Int := if p 160 then d12 p else d4161 p
theorem agree4162 (p q : Pattern) (h : Agree support p q) : d4162 p = d4162 q := by
  simp only [d4162, h 160 (by decide), agree12 p q h, agree4161 p q h]
theorem nonnegative4162 (p : Pattern) : 0 ≤ d4162 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4161 p)
def d4163 (p : Pattern) : Int := if p 138 then d4162 p else d4158 p
theorem agree4163 (p q : Pattern) (h : Agree support p q) : d4163 p = d4163 q := by
  simp only [d4163, h 138 (by decide), agree4162 p q h, agree4158 p q h]
theorem nonnegative4163 (p : Pattern) : 0 ≤ d4163 p :=
  nonnegative_ite (p 138) (nonnegative4162 p) (nonnegative4158 p)
def d4164 (p : Pattern) : Int := if p 116 then d4163 p else d4159 p
theorem agree4164 (p q : Pattern) (h : Agree support p q) : d4164 p = d4164 q := by
  simp only [d4164, h 116 (by decide), agree4163 p q h, agree4159 p q h]
theorem nonnegative4164 (p : Pattern) : 0 ≤ d4164 p :=
  nonnegative_ite (p 116) (nonnegative4163 p) (nonnegative4159 p)
def d4165 (p : Pattern) : Int := if p 138 then d12 p else d4158 p
theorem agree4165 (p q : Pattern) (h : Agree support p q) : d4165 p = d4165 q := by
  simp only [d4165, h 138 (by decide), agree12 p q h, agree4158 p q h]
theorem nonnegative4165 (p : Pattern) : 0 ≤ d4165 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4158 p)
def d4166 (p : Pattern) : Int := if p 116 then d4165 p else d4159 p
theorem agree4166 (p q : Pattern) (h : Agree support p q) : d4166 p = d4166 q := by
  simp only [d4166, h 116 (by decide), agree4165 p q h, agree4159 p q h]
theorem nonnegative4166 (p : Pattern) : 0 ≤ d4166 p :=
  nonnegative_ite (p 116) (nonnegative4165 p) (nonnegative4159 p)
def d4167 (p : Pattern) : Int := if p 115 then d4166 p else d4164 p
theorem agree4167 (p q : Pattern) (h : Agree support p q) : d4167 p = d4167 q := by
  simp only [d4167, h 115 (by decide), agree4166 p q h, agree4164 p q h]
theorem nonnegative4167 (p : Pattern) : 0 ≤ d4167 p :=
  nonnegative_ite (p 115) (nonnegative4166 p) (nonnegative4164 p)
def d4168 (p : Pattern) : Int := if p 162 then d109 p else d105 p
theorem agree4168 (p q : Pattern) (h : Agree support p q) : d4168 p = d4168 q := by
  simp only [d4168, h 162 (by decide), agree109 p q h, agree105 p q h]
theorem nonnegative4168 (p : Pattern) : 0 ≤ d4168 p :=
  nonnegative_ite (p 162) (nonnegative109 p) (nonnegative105 p)
def d4169 (p : Pattern) : Int := if p 161 then d1140 p else d4168 p
theorem agree4169 (p q : Pattern) (h : Agree support p q) : d4169 p = d4169 q := by
  simp only [d4169, h 161 (by decide), agree1140 p q h, agree4168 p q h]
theorem nonnegative4169 (p : Pattern) : 0 ≤ d4169 p :=
  nonnegative_ite (p 161) (nonnegative1140 p) (nonnegative4168 p)
def d4170 (p : Pattern) : Int := if p 162 then d125 p else d122 p
theorem agree4170 (p q : Pattern) (h : Agree support p q) : d4170 p = d4170 q := by
  simp only [d4170, h 162 (by decide), agree125 p q h, agree122 p q h]
theorem nonnegative4170 (p : Pattern) : 0 ≤ d4170 p :=
  nonnegative_ite (p 162) (nonnegative125 p) (nonnegative122 p)
def d4171 (p : Pattern) : Int := if p 162 then d12 p else d125 p
theorem agree4171 (p q : Pattern) (h : Agree support p q) : d4171 p = d4171 q := by
  simp only [d4171, h 162 (by decide), agree12 p q h, agree125 p q h]
theorem nonnegative4171 (p : Pattern) : 0 ≤ d4171 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative125 p)
def d4172 (p : Pattern) : Int := if p 161 then d4171 p else d4170 p
theorem agree4172 (p q : Pattern) (h : Agree support p q) : d4172 p = d4172 q := by
  simp only [d4172, h 161 (by decide), agree4171 p q h, agree4170 p q h]
theorem nonnegative4172 (p : Pattern) : 0 ≤ d4172 p :=
  nonnegative_ite (p 161) (nonnegative4171 p) (nonnegative4170 p)
def d4173 (p : Pattern) : Int := if p 160 then d4172 p else d4169 p
theorem agree4173 (p q : Pattern) (h : Agree support p q) : d4173 p = d4173 q := by
  simp only [d4173, h 160 (by decide), agree4172 p q h, agree4169 p q h]
theorem nonnegative4173 (p : Pattern) : 0 ≤ d4173 p :=
  nonnegative_ite (p 160) (nonnegative4172 p) (nonnegative4169 p)
def d4174 (p : Pattern) : Int := if p 162 then d12 p else d148 p
theorem agree4174 (p q : Pattern) (h : Agree support p q) : d4174 p = d4174 q := by
  simp only [d4174, h 162 (by decide), agree12 p q h, agree148 p q h]
theorem nonnegative4174 (p : Pattern) : 0 ≤ d4174 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative148 p)
def d4175 (p : Pattern) : Int := if p 161 then d12 p else d4174 p
theorem agree4175 (p q : Pattern) (h : Agree support p q) : d4175 p = d4175 q := by
  simp only [d4175, h 161 (by decide), agree12 p q h, agree4174 p q h]
theorem nonnegative4175 (p : Pattern) : 0 ≤ d4175 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4174 p)
def d4176 (p : Pattern) : Int := if p 160 then d4175 p else d4169 p
theorem agree4176 (p q : Pattern) (h : Agree support p q) : d4176 p = d4176 q := by
  simp only [d4176, h 160 (by decide), agree4175 p q h, agree4169 p q h]
theorem nonnegative4176 (p : Pattern) : 0 ≤ d4176 p :=
  nonnegative_ite (p 160) (nonnegative4175 p) (nonnegative4169 p)
def d4177 (p : Pattern) : Int := if p 138 then d4176 p else d4173 p
theorem agree4177 (p q : Pattern) (h : Agree support p q) : d4177 p = d4177 q := by
  simp only [d4177, h 138 (by decide), agree4176 p q h, agree4173 p q h]
theorem nonnegative4177 (p : Pattern) : 0 ≤ d4177 p :=
  nonnegative_ite (p 138) (nonnegative4176 p) (nonnegative4173 p)
def d4178 (p : Pattern) : Int := if p 138 then d12 p else d4176 p
theorem agree4178 (p q : Pattern) (h : Agree support p q) : d4178 p = d4178 q := by
  simp only [d4178, h 138 (by decide), agree12 p q h, agree4176 p q h]
theorem nonnegative4178 (p : Pattern) : 0 ≤ d4178 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4176 p)
def d4179 (p : Pattern) : Int := if p 116 then d4178 p else d4177 p
theorem agree4179 (p q : Pattern) (h : Agree support p q) : d4179 p = d4179 q := by
  simp only [d4179, h 116 (by decide), agree4178 p q h, agree4177 p q h]
theorem nonnegative4179 (p : Pattern) : 0 ≤ d4179 p :=
  nonnegative_ite (p 116) (nonnegative4178 p) (nonnegative4177 p)
def d4180 (p : Pattern) : Int := if p 71 then d4179 p else d4167 p
theorem agree4180 (p q : Pattern) (h : Agree support p q) : d4180 p = d4180 q := by
  simp only [d4180, h 71 (by decide), agree4179 p q h, agree4167 p q h]
theorem nonnegative4180 (p : Pattern) : 0 ≤ d4180 p :=
  nonnegative_ite (p 71) (nonnegative4179 p) (nonnegative4167 p)
def d4181 (p : Pattern) : Int := if p 49 then d4180 p else d4167 p
theorem agree4181 (p q : Pattern) (h : Agree support p q) : d4181 p = d4181 q := by
  simp only [d4181, h 49 (by decide), agree4180 p q h, agree4167 p q h]
theorem nonnegative4181 (p : Pattern) : 0 ≤ d4181 p :=
  nonnegative_ite (p 49) (nonnegative4180 p) (nonnegative4167 p)
def d4182 (p : Pattern) : Int := if p 162 then d274 p else d270 p
theorem agree4182 (p q : Pattern) (h : Agree support p q) : d4182 p = d4182 q := by
  simp only [d4182, h 162 (by decide), agree274 p q h, agree270 p q h]
theorem nonnegative4182 (p : Pattern) : 0 ≤ d4182 p :=
  nonnegative_ite (p 162) (nonnegative274 p) (nonnegative270 p)
def d4183 (p : Pattern) : Int := if p 162 then d12 p else d274 p
theorem agree4183 (p q : Pattern) (h : Agree support p q) : d4183 p = d4183 q := by
  simp only [d4183, h 162 (by decide), agree12 p q h, agree274 p q h]
theorem nonnegative4183 (p : Pattern) : 0 ≤ d4183 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative274 p)
def d4184 (p : Pattern) : Int := if p 161 then d4183 p else d4182 p
theorem agree4184 (p q : Pattern) (h : Agree support p q) : d4184 p = d4184 q := by
  simp only [d4184, h 161 (by decide), agree4183 p q h, agree4182 p q h]
theorem nonnegative4184 (p : Pattern) : 0 ≤ d4184 p :=
  nonnegative_ite (p 161) (nonnegative4183 p) (nonnegative4182 p)
def d4185 (p : Pattern) : Int := if p 160 then d4184 p else d4169 p
theorem agree4185 (p q : Pattern) (h : Agree support p q) : d4185 p = d4185 q := by
  simp only [d4185, h 160 (by decide), agree4184 p q h, agree4169 p q h]
theorem nonnegative4185 (p : Pattern) : 0 ≤ d4185 p :=
  nonnegative_ite (p 160) (nonnegative4184 p) (nonnegative4169 p)
def d4186 (p : Pattern) : Int := if p 162 then d292 p else d269 p
theorem agree4186 (p q : Pattern) (h : Agree support p q) : d4186 p = d4186 q := by
  simp only [d4186, h 162 (by decide), agree292 p q h, agree269 p q h]
theorem nonnegative4186 (p : Pattern) : 0 ≤ d4186 p :=
  nonnegative_ite (p 162) (nonnegative292 p) (nonnegative269 p)
def d4187 (p : Pattern) : Int := if p 162 then d12 p else d292 p
theorem agree4187 (p q : Pattern) (h : Agree support p q) : d4187 p = d4187 q := by
  simp only [d4187, h 162 (by decide), agree12 p q h, agree292 p q h]
theorem nonnegative4187 (p : Pattern) : 0 ≤ d4187 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative292 p)
def d4188 (p : Pattern) : Int := if p 161 then d4187 p else d4186 p
theorem agree4188 (p q : Pattern) (h : Agree support p q) : d4188 p = d4188 q := by
  simp only [d4188, h 161 (by decide), agree4187 p q h, agree4186 p q h]
theorem nonnegative4188 (p : Pattern) : 0 ≤ d4188 p :=
  nonnegative_ite (p 161) (nonnegative4187 p) (nonnegative4186 p)
def d4189 (p : Pattern) : Int := if p 160 then d4175 p else d4188 p
theorem agree4189 (p q : Pattern) (h : Agree support p q) : d4189 p = d4189 q := by
  simp only [d4189, h 160 (by decide), agree4175 p q h, agree4188 p q h]
theorem nonnegative4189 (p : Pattern) : 0 ≤ d4189 p :=
  nonnegative_ite (p 160) (nonnegative4175 p) (nonnegative4188 p)
def d4190 (p : Pattern) : Int := if p 138 then d4189 p else d4185 p
theorem agree4190 (p q : Pattern) (h : Agree support p q) : d4190 p = d4190 q := by
  simp only [d4190, h 138 (by decide), agree4189 p q h, agree4185 p q h]
theorem nonnegative4190 (p : Pattern) : 0 ≤ d4190 p :=
  nonnegative_ite (p 138) (nonnegative4189 p) (nonnegative4185 p)
def d4191 (p : Pattern) : Int := if p 138 then d12 p else d4189 p
theorem agree4191 (p q : Pattern) (h : Agree support p q) : d4191 p = d4191 q := by
  simp only [d4191, h 138 (by decide), agree12 p q h, agree4189 p q h]
theorem nonnegative4191 (p : Pattern) : 0 ≤ d4191 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4189 p)
def d4192 (p : Pattern) : Int := if p 116 then d4191 p else d4190 p
theorem agree4192 (p q : Pattern) (h : Agree support p q) : d4192 p = d4192 q := by
  simp only [d4192, h 116 (by decide), agree4191 p q h, agree4190 p q h]
theorem nonnegative4192 (p : Pattern) : 0 ≤ d4192 p :=
  nonnegative_ite (p 116) (nonnegative4191 p) (nonnegative4190 p)
def d4193 (p : Pattern) : Int := if p 115 then d4192 p else d4179 p
theorem agree4193 (p q : Pattern) (h : Agree support p q) : d4193 p = d4193 q := by
  simp only [d4193, h 115 (by decide), agree4192 p q h, agree4179 p q h]
theorem nonnegative4193 (p : Pattern) : 0 ≤ d4193 p :=
  nonnegative_ite (p 115) (nonnegative4192 p) (nonnegative4179 p)
def d4194 (p : Pattern) : Int := if p 71 then d4193 p else d4167 p
theorem agree4194 (p q : Pattern) (h : Agree support p q) : d4194 p = d4194 q := by
  simp only [d4194, h 71 (by decide), agree4193 p q h, agree4167 p q h]
theorem nonnegative4194 (p : Pattern) : 0 ≤ d4194 p :=
  nonnegative_ite (p 71) (nonnegative4193 p) (nonnegative4167 p)
def d4195 (p : Pattern) : Int := if p 49 then d4194 p else d4167 p
theorem agree4195 (p q : Pattern) (h : Agree support p q) : d4195 p = d4195 q := by
  simp only [d4195, h 49 (by decide), agree4194 p q h, agree4167 p q h]
theorem nonnegative4195 (p : Pattern) : 0 ≤ d4195 p :=
  nonnegative_ite (p 49) (nonnegative4194 p) (nonnegative4167 p)
def d4196 (p : Pattern) : Int := if p 48 then d4195 p else d4181 p
theorem agree4196 (p q : Pattern) (h : Agree support p q) : d4196 p = d4196 q := by
  simp only [d4196, h 48 (by decide), agree4195 p q h, agree4181 p q h]
theorem nonnegative4196 (p : Pattern) : 0 ≤ d4196 p :=
  nonnegative_ite (p 48) (nonnegative4195 p) (nonnegative4181 p)
def d4197 (p : Pattern) : Int := if p 71 then d158 p else d88 p
theorem agree4197 (p q : Pattern) (h : Agree support p q) : d4197 p = d4197 q := by
  simp only [d4197, h 71 (by decide), agree158 p q h, agree88 p q h]
theorem nonnegative4197 (p : Pattern) : 0 ≤ d4197 p :=
  nonnegative_ite (p 71) (nonnegative158 p) (nonnegative88 p)
def d4198 (p : Pattern) : Int := if p 49 then d4197 p else d88 p
theorem agree4198 (p q : Pattern) (h : Agree support p q) : d4198 p = d4198 q := by
  simp only [d4198, h 49 (by decide), agree4197 p q h, agree88 p q h]
theorem nonnegative4198 (p : Pattern) : 0 ≤ d4198 p :=
  nonnegative_ite (p 49) (nonnegative4197 p) (nonnegative88 p)
def d4199 (p : Pattern) : Int := if p 115 then d306 p else d223 p
theorem agree4199 (p q : Pattern) (h : Agree support p q) : d4199 p = d4199 q := by
  simp only [d4199, h 115 (by decide), agree306 p q h, agree223 p q h]
theorem nonnegative4199 (p : Pattern) : 0 ≤ d4199 p :=
  nonnegative_ite (p 115) (nonnegative306 p) (nonnegative223 p)
end NetHack.Sokoban22Refined85
