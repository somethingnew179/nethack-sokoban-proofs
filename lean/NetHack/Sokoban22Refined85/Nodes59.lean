/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes58
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7080 (p : Pattern) : Int := if p 182 then d12 p else d1942 p
theorem agree7080 (p q : Pattern) (h : Agree support p q) : d7080 p = d7080 q := by
  simp only [d7080, h 182 (by decide), agree12 p q h, agree1942 p q h]
theorem nonnegative7080 (p : Pattern) : 0 ≤ d7080 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1942 p)
def d7081 (p : Pattern) : Int := if p 182 then d12 p else d2130 p
theorem agree7081 (p q : Pattern) (h : Agree support p q) : d7081 p = d7081 q := by
  simp only [d7081, h 182 (by decide), agree12 p q h, agree2130 p q h]
theorem nonnegative7081 (p : Pattern) : 0 ≤ d7081 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2130 p)
def d7082 (p : Pattern) : Int := if p 163 then d7081 p else d7080 p
theorem agree7082 (p q : Pattern) (h : Agree support p q) : d7082 p = d7082 q := by
  simp only [d7082, h 163 (by decide), agree7081 p q h, agree7080 p q h]
theorem nonnegative7082 (p : Pattern) : 0 ≤ d7082 p :=
  nonnegative_ite (p 163) (nonnegative7081 p) (nonnegative7080 p)
def d7083 (p : Pattern) : Int := if p 162 then d7082 p else d7080 p
theorem agree7083 (p q : Pattern) (h : Agree support p q) : d7083 p = d7083 q := by
  simp only [d7083, h 162 (by decide), agree7082 p q h, agree7080 p q h]
theorem nonnegative7083 (p : Pattern) : 0 ≤ d7083 p :=
  nonnegative_ite (p 162) (nonnegative7082 p) (nonnegative7080 p)
def d7084 (p : Pattern) : Int := if p 163 then d12 p else d7033 p
theorem agree7084 (p q : Pattern) (h : Agree support p q) : d7084 p = d7084 q := by
  simp only [d7084, h 163 (by decide), agree12 p q h, agree7033 p q h]
theorem nonnegative7084 (p : Pattern) : 0 ≤ d7084 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7033 p)
def d7085 (p : Pattern) : Int := if p 162 then d7084 p else d7082 p
theorem agree7085 (p q : Pattern) (h : Agree support p q) : d7085 p = d7085 q := by
  simp only [d7085, h 162 (by decide), agree7084 p q h, agree7082 p q h]
theorem nonnegative7085 (p : Pattern) : 0 ≤ d7085 p :=
  nonnegative_ite (p 162) (nonnegative7084 p) (nonnegative7082 p)
def d7086 (p : Pattern) : Int := if p 161 then d7085 p else d7083 p
theorem agree7086 (p q : Pattern) (h : Agree support p q) : d7086 p = d7086 q := by
  simp only [d7086, h 161 (by decide), agree7085 p q h, agree7083 p q h]
theorem nonnegative7086 (p : Pattern) : 0 ≤ d7086 p :=
  nonnegative_ite (p 161) (nonnegative7085 p) (nonnegative7083 p)
def d7087 (p : Pattern) : Int := if p 182 then d12 p else d1957 p
theorem agree7087 (p q : Pattern) (h : Agree support p q) : d7087 p = d7087 q := by
  simp only [d7087, h 182 (by decide), agree12 p q h, agree1957 p q h]
theorem nonnegative7087 (p : Pattern) : 0 ≤ d7087 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1957 p)
def d7088 (p : Pattern) : Int := if p 182 then d12 p else d1966 p
theorem agree7088 (p q : Pattern) (h : Agree support p q) : d7088 p = d7088 q := by
  simp only [d7088, h 182 (by decide), agree12 p q h, agree1966 p q h]
theorem nonnegative7088 (p : Pattern) : 0 ≤ d7088 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1966 p)
def d7089 (p : Pattern) : Int := if p 163 then d7088 p else d7087 p
theorem agree7089 (p q : Pattern) (h : Agree support p q) : d7089 p = d7089 q := by
  simp only [d7089, h 163 (by decide), agree7088 p q h, agree7087 p q h]
theorem nonnegative7089 (p : Pattern) : 0 ≤ d7089 p :=
  nonnegative_ite (p 163) (nonnegative7088 p) (nonnegative7087 p)
def d7090 (p : Pattern) : Int := if p 162 then d7089 p else d7087 p
theorem agree7090 (p q : Pattern) (h : Agree support p q) : d7090 p = d7090 q := by
  simp only [d7090, h 162 (by decide), agree7089 p q h, agree7087 p q h]
theorem nonnegative7090 (p : Pattern) : 0 ≤ d7090 p :=
  nonnegative_ite (p 162) (nonnegative7089 p) (nonnegative7087 p)
def d7091 (p : Pattern) : Int := if p 162 then d7084 p else d7089 p
theorem agree7091 (p q : Pattern) (h : Agree support p q) : d7091 p = d7091 q := by
  simp only [d7091, h 162 (by decide), agree7084 p q h, agree7089 p q h]
theorem nonnegative7091 (p : Pattern) : 0 ≤ d7091 p :=
  nonnegative_ite (p 162) (nonnegative7084 p) (nonnegative7089 p)
def d7092 (p : Pattern) : Int := if p 161 then d7091 p else d7090 p
theorem agree7092 (p q : Pattern) (h : Agree support p q) : d7092 p = d7092 q := by
  simp only [d7092, h 161 (by decide), agree7091 p q h, agree7090 p q h]
theorem nonnegative7092 (p : Pattern) : 0 ≤ d7092 p :=
  nonnegative_ite (p 161) (nonnegative7091 p) (nonnegative7090 p)
def d7093 (p : Pattern) : Int := if p 160 then d7092 p else d7086 p
theorem agree7093 (p q : Pattern) (h : Agree support p q) : d7093 p = d7093 q := by
  simp only [d7093, h 160 (by decide), agree7092 p q h, agree7086 p q h]
theorem nonnegative7093 (p : Pattern) : 0 ≤ d7093 p :=
  nonnegative_ite (p 160) (nonnegative7092 p) (nonnegative7086 p)
def d7094 (p : Pattern) : Int := if p 182 then d12 p else d2125 p
theorem agree7094 (p q : Pattern) (h : Agree support p q) : d7094 p = d7094 q := by
  simp only [d7094, h 182 (by decide), agree12 p q h, agree2125 p q h]
theorem nonnegative7094 (p : Pattern) : 0 ≤ d7094 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2125 p)
def d7095 (p : Pattern) : Int := if p 163 then d7094 p else d7080 p
theorem agree7095 (p q : Pattern) (h : Agree support p q) : d7095 p = d7095 q := by
  simp only [d7095, h 163 (by decide), agree7094 p q h, agree7080 p q h]
theorem nonnegative7095 (p : Pattern) : 0 ≤ d7095 p :=
  nonnegative_ite (p 163) (nonnegative7094 p) (nonnegative7080 p)
def d7096 (p : Pattern) : Int := if p 163 then d7033 p else d7081 p
theorem agree7096 (p q : Pattern) (h : Agree support p q) : d7096 p = d7096 q := by
  simp only [d7096, h 163 (by decide), agree7033 p q h, agree7081 p q h]
theorem nonnegative7096 (p : Pattern) : 0 ≤ d7096 p :=
  nonnegative_ite (p 163) (nonnegative7033 p) (nonnegative7081 p)
def d7097 (p : Pattern) : Int := if p 162 then d7096 p else d7095 p
theorem agree7097 (p q : Pattern) (h : Agree support p q) : d7097 p = d7097 q := by
  simp only [d7097, h 162 (by decide), agree7096 p q h, agree7095 p q h]
theorem nonnegative7097 (p : Pattern) : 0 ≤ d7097 p :=
  nonnegative_ite (p 162) (nonnegative7096 p) (nonnegative7095 p)
def d7098 (p : Pattern) : Int := if p 163 then d7035 p else d7081 p
theorem agree7098 (p q : Pattern) (h : Agree support p q) : d7098 p = d7098 q := by
  simp only [d7098, h 163 (by decide), agree7035 p q h, agree7081 p q h]
theorem nonnegative7098 (p : Pattern) : 0 ≤ d7098 p :=
  nonnegative_ite (p 163) (nonnegative7035 p) (nonnegative7081 p)
def d7099 (p : Pattern) : Int := if p 162 then d12 p else d7098 p
theorem agree7099 (p q : Pattern) (h : Agree support p q) : d7099 p = d7099 q := by
  simp only [d7099, h 162 (by decide), agree12 p q h, agree7098 p q h]
theorem nonnegative7099 (p : Pattern) : 0 ≤ d7099 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7098 p)
def d7100 (p : Pattern) : Int := if p 161 then d7099 p else d7097 p
theorem agree7100 (p q : Pattern) (h : Agree support p q) : d7100 p = d7100 q := by
  simp only [d7100, h 161 (by decide), agree7099 p q h, agree7097 p q h]
theorem nonnegative7100 (p : Pattern) : 0 ≤ d7100 p :=
  nonnegative_ite (p 161) (nonnegative7099 p) (nonnegative7097 p)
def d7101 (p : Pattern) : Int := if p 182 then d12 p else d1898 p
theorem agree7101 (p q : Pattern) (h : Agree support p q) : d7101 p = d7101 q := by
  simp only [d7101, h 182 (by decide), agree12 p q h, agree1898 p q h]
theorem nonnegative7101 (p : Pattern) : 0 ≤ d7101 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1898 p)
def d7102 (p : Pattern) : Int := if p 163 then d7101 p else d7087 p
theorem agree7102 (p q : Pattern) (h : Agree support p q) : d7102 p = d7102 q := by
  simp only [d7102, h 163 (by decide), agree7101 p q h, agree7087 p q h]
theorem nonnegative7102 (p : Pattern) : 0 ≤ d7102 p :=
  nonnegative_ite (p 163) (nonnegative7101 p) (nonnegative7087 p)
def d7103 (p : Pattern) : Int := if p 163 then d7033 p else d7088 p
theorem agree7103 (p q : Pattern) (h : Agree support p q) : d7103 p = d7103 q := by
  simp only [d7103, h 163 (by decide), agree7033 p q h, agree7088 p q h]
theorem nonnegative7103 (p : Pattern) : 0 ≤ d7103 p :=
  nonnegative_ite (p 163) (nonnegative7033 p) (nonnegative7088 p)
def d7104 (p : Pattern) : Int := if p 162 then d7103 p else d7102 p
theorem agree7104 (p q : Pattern) (h : Agree support p q) : d7104 p = d7104 q := by
  simp only [d7104, h 162 (by decide), agree7103 p q h, agree7102 p q h]
theorem nonnegative7104 (p : Pattern) : 0 ≤ d7104 p :=
  nonnegative_ite (p 162) (nonnegative7103 p) (nonnegative7102 p)
def d7105 (p : Pattern) : Int := if p 163 then d7035 p else d7088 p
theorem agree7105 (p q : Pattern) (h : Agree support p q) : d7105 p = d7105 q := by
  simp only [d7105, h 163 (by decide), agree7035 p q h, agree7088 p q h]
theorem nonnegative7105 (p : Pattern) : 0 ≤ d7105 p :=
  nonnegative_ite (p 163) (nonnegative7035 p) (nonnegative7088 p)
def d7106 (p : Pattern) : Int := if p 162 then d12 p else d7105 p
theorem agree7106 (p q : Pattern) (h : Agree support p q) : d7106 p = d7106 q := by
  simp only [d7106, h 162 (by decide), agree12 p q h, agree7105 p q h]
theorem nonnegative7106 (p : Pattern) : 0 ≤ d7106 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7105 p)
def d7107 (p : Pattern) : Int := if p 161 then d7106 p else d7104 p
theorem agree7107 (p q : Pattern) (h : Agree support p q) : d7107 p = d7107 q := by
  simp only [d7107, h 161 (by decide), agree7106 p q h, agree7104 p q h]
theorem nonnegative7107 (p : Pattern) : 0 ≤ d7107 p :=
  nonnegative_ite (p 161) (nonnegative7106 p) (nonnegative7104 p)
def d7108 (p : Pattern) : Int := if p 160 then d7107 p else d7100 p
theorem agree7108 (p q : Pattern) (h : Agree support p q) : d7108 p = d7108 q := by
  simp only [d7108, h 160 (by decide), agree7107 p q h, agree7100 p q h]
theorem nonnegative7108 (p : Pattern) : 0 ≤ d7108 p :=
  nonnegative_ite (p 160) (nonnegative7107 p) (nonnegative7100 p)
def d7109 (p : Pattern) : Int := if p 141 then d7108 p else d7093 p
theorem agree7109 (p q : Pattern) (h : Agree support p q) : d7109 p = d7109 q := by
  simp only [d7109, h 141 (by decide), agree7108 p q h, agree7093 p q h]
theorem nonnegative7109 (p : Pattern) : 0 ≤ d7109 p :=
  nonnegative_ite (p 141) (nonnegative7108 p) (nonnegative7093 p)
def d7110 (p : Pattern) : Int := if p 182 then d12 p else d2108 p
theorem agree7110 (p q : Pattern) (h : Agree support p q) : d7110 p = d7110 q := by
  simp only [d7110, h 182 (by decide), agree12 p q h, agree2108 p q h]
theorem nonnegative7110 (p : Pattern) : 0 ≤ d7110 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2108 p)
def d7111 (p : Pattern) : Int := if p 182 then d12 p else d3038 p
theorem agree7111 (p q : Pattern) (h : Agree support p q) : d7111 p = d7111 q := by
  simp only [d7111, h 182 (by decide), agree12 p q h, agree3038 p q h]
theorem nonnegative7111 (p : Pattern) : 0 ≤ d7111 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3038 p)
def d7112 (p : Pattern) : Int := if p 163 then d7111 p else d7110 p
theorem agree7112 (p q : Pattern) (h : Agree support p q) : d7112 p = d7112 q := by
  simp only [d7112, h 163 (by decide), agree7111 p q h, agree7110 p q h]
theorem nonnegative7112 (p : Pattern) : 0 ≤ d7112 p :=
  nonnegative_ite (p 163) (nonnegative7111 p) (nonnegative7110 p)
def d7113 (p : Pattern) : Int := if p 162 then d7089 p else d7112 p
theorem agree7113 (p q : Pattern) (h : Agree support p q) : d7113 p = d7113 q := by
  simp only [d7113, h 162 (by decide), agree7089 p q h, agree7112 p q h]
theorem nonnegative7113 (p : Pattern) : 0 ≤ d7113 p :=
  nonnegative_ite (p 162) (nonnegative7089 p) (nonnegative7112 p)
def d7114 (p : Pattern) : Int := if p 161 then d7091 p else d7113 p
theorem agree7114 (p q : Pattern) (h : Agree support p q) : d7114 p = d7114 q := by
  simp only [d7114, h 161 (by decide), agree7091 p q h, agree7113 p q h]
theorem nonnegative7114 (p : Pattern) : 0 ≤ d7114 p :=
  nonnegative_ite (p 161) (nonnegative7091 p) (nonnegative7113 p)
def d7115 (p : Pattern) : Int := if p 182 then d12 p else d1905 p
theorem agree7115 (p q : Pattern) (h : Agree support p q) : d7115 p = d7115 q := by
  simp only [d7115, h 182 (by decide), agree12 p q h, agree1905 p q h]
theorem nonnegative7115 (p : Pattern) : 0 ≤ d7115 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1905 p)
def d7116 (p : Pattern) : Int := if p 163 then d7115 p else d7101 p
theorem agree7116 (p q : Pattern) (h : Agree support p q) : d7116 p = d7116 q := by
  simp only [d7116, h 163 (by decide), agree7115 p q h, agree7101 p q h]
theorem nonnegative7116 (p : Pattern) : 0 ≤ d7116 p :=
  nonnegative_ite (p 163) (nonnegative7115 p) (nonnegative7101 p)
def d7117 (p : Pattern) : Int := if p 162 then d12 p else d7116 p
theorem agree7117 (p q : Pattern) (h : Agree support p q) : d7117 p = d7117 q := by
  simp only [d7117, h 162 (by decide), agree12 p q h, agree7116 p q h]
theorem nonnegative7117 (p : Pattern) : 0 ≤ d7117 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7116 p)
def d7118 (p : Pattern) : Int := if p 161 then d12 p else d7117 p
theorem agree7118 (p q : Pattern) (h : Agree support p q) : d7118 p = d7118 q := by
  simp only [d7118, h 161 (by decide), agree12 p q h, agree7117 p q h]
theorem nonnegative7118 (p : Pattern) : 0 ≤ d7118 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7117 p)
def d7119 (p : Pattern) : Int := if p 160 then d7118 p else d7114 p
theorem agree7119 (p q : Pattern) (h : Agree support p q) : d7119 p = d7119 q := by
  simp only [d7119, h 160 (by decide), agree7118 p q h, agree7114 p q h]
theorem nonnegative7119 (p : Pattern) : 0 ≤ d7119 p :=
  nonnegative_ite (p 160) (nonnegative7118 p) (nonnegative7114 p)
def d7120 (p : Pattern) : Int := if p 163 then d7101 p else d7111 p
theorem agree7120 (p q : Pattern) (h : Agree support p q) : d7120 p = d7120 q := by
  simp only [d7120, h 163 (by decide), agree7101 p q h, agree7111 p q h]
theorem nonnegative7120 (p : Pattern) : 0 ≤ d7120 p :=
  nonnegative_ite (p 163) (nonnegative7101 p) (nonnegative7111 p)
def d7121 (p : Pattern) : Int := if p 162 then d7103 p else d7120 p
theorem agree7121 (p q : Pattern) (h : Agree support p q) : d7121 p = d7121 q := by
  simp only [d7121, h 162 (by decide), agree7103 p q h, agree7120 p q h]
theorem nonnegative7121 (p : Pattern) : 0 ≤ d7121 p :=
  nonnegative_ite (p 162) (nonnegative7103 p) (nonnegative7120 p)
def d7122 (p : Pattern) : Int := if p 161 then d7106 p else d7121 p
theorem agree7122 (p q : Pattern) (h : Agree support p q) : d7122 p = d7122 q := by
  simp only [d7122, h 161 (by decide), agree7106 p q h, agree7121 p q h]
theorem nonnegative7122 (p : Pattern) : 0 ≤ d7122 p :=
  nonnegative_ite (p 161) (nonnegative7106 p) (nonnegative7121 p)
def d7123 (p : Pattern) : Int := if p 163 then d12 p else d7115 p
theorem agree7123 (p q : Pattern) (h : Agree support p q) : d7123 p = d7123 q := by
  simp only [d7123, h 163 (by decide), agree12 p q h, agree7115 p q h]
theorem nonnegative7123 (p : Pattern) : 0 ≤ d7123 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7115 p)
def d7124 (p : Pattern) : Int := if p 162 then d12 p else d7123 p
theorem agree7124 (p q : Pattern) (h : Agree support p q) : d7124 p = d7124 q := by
  simp only [d7124, h 162 (by decide), agree12 p q h, agree7123 p q h]
theorem nonnegative7124 (p : Pattern) : 0 ≤ d7124 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7123 p)
def d7125 (p : Pattern) : Int := if p 161 then d12 p else d7124 p
theorem agree7125 (p q : Pattern) (h : Agree support p q) : d7125 p = d7125 q := by
  simp only [d7125, h 161 (by decide), agree12 p q h, agree7124 p q h]
theorem nonnegative7125 (p : Pattern) : 0 ≤ d7125 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7124 p)
def d7126 (p : Pattern) : Int := if p 160 then d7125 p else d7122 p
theorem agree7126 (p q : Pattern) (h : Agree support p q) : d7126 p = d7126 q := by
  simp only [d7126, h 160 (by decide), agree7125 p q h, agree7122 p q h]
theorem nonnegative7126 (p : Pattern) : 0 ≤ d7126 p :=
  nonnegative_ite (p 160) (nonnegative7125 p) (nonnegative7122 p)
def d7127 (p : Pattern) : Int := if p 141 then d7126 p else d7119 p
theorem agree7127 (p q : Pattern) (h : Agree support p q) : d7127 p = d7127 q := by
  simp only [d7127, h 141 (by decide), agree7126 p q h, agree7119 p q h]
theorem nonnegative7127 (p : Pattern) : 0 ≤ d7127 p :=
  nonnegative_ite (p 141) (nonnegative7126 p) (nonnegative7119 p)
def d7128 (p : Pattern) : Int := if p 138 then d7127 p else d7109 p
theorem agree7128 (p q : Pattern) (h : Agree support p q) : d7128 p = d7128 q := by
  simp only [d7128, h 138 (by decide), agree7127 p q h, agree7109 p q h]
theorem nonnegative7128 (p : Pattern) : 0 ≤ d7128 p :=
  nonnegative_ite (p 138) (nonnegative7127 p) (nonnegative7109 p)
def d7129 (p : Pattern) : Int := if p 162 then d12 p else d7084 p
theorem agree7129 (p q : Pattern) (h : Agree support p q) : d7129 p = d7129 q := by
  simp only [d7129, h 162 (by decide), agree12 p q h, agree7084 p q h]
theorem nonnegative7129 (p : Pattern) : 0 ≤ d7129 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7084 p)
def d7130 (p : Pattern) : Int := if p 161 then d12 p else d7129 p
theorem agree7130 (p q : Pattern) (h : Agree support p q) : d7130 p = d7130 q := by
  simp only [d7130, h 161 (by decide), agree12 p q h, agree7129 p q h]
theorem nonnegative7130 (p : Pattern) : 0 ≤ d7130 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7129 p)
def d7131 (p : Pattern) : Int := if p 160 then d12 p else d7130 p
theorem agree7131 (p q : Pattern) (h : Agree support p q) : d7131 p = d7131 q := by
  simp only [d7131, h 160 (by decide), agree12 p q h, agree7130 p q h]
theorem nonnegative7131 (p : Pattern) : 0 ≤ d7131 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative7130 p)
def d7132 (p : Pattern) : Int := if p 141 then d12 p else d7131 p
theorem agree7132 (p q : Pattern) (h : Agree support p q) : d7132 p = d7132 q := by
  simp only [d7132, h 141 (by decide), agree12 p q h, agree7131 p q h]
theorem nonnegative7132 (p : Pattern) : 0 ≤ d7132 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative7131 p)
def d7133 (p : Pattern) : Int := if p 138 then d7132 p else d7127 p
theorem agree7133 (p q : Pattern) (h : Agree support p q) : d7133 p = d7133 q := by
  simp only [d7133, h 138 (by decide), agree7132 p q h, agree7127 p q h]
theorem nonnegative7133 (p : Pattern) : 0 ≤ d7133 p :=
  nonnegative_ite (p 138) (nonnegative7132 p) (nonnegative7127 p)
def d7134 (p : Pattern) : Int := if p 116 then d7133 p else d7128 p
theorem agree7134 (p q : Pattern) (h : Agree support p q) : d7134 p = d7134 q := by
  simp only [d7134, h 116 (by decide), agree7133 p q h, agree7128 p q h]
theorem nonnegative7134 (p : Pattern) : 0 ≤ d7134 p :=
  nonnegative_ite (p 116) (nonnegative7133 p) (nonnegative7128 p)
def d7135 (p : Pattern) : Int := if p 138 then d12 p else d7127 p
theorem agree7135 (p q : Pattern) (h : Agree support p q) : d7135 p = d7135 q := by
  simp only [d7135, h 138 (by decide), agree12 p q h, agree7127 p q h]
theorem nonnegative7135 (p : Pattern) : 0 ≤ d7135 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7127 p)
def d7136 (p : Pattern) : Int := if p 116 then d7135 p else d7128 p
theorem agree7136 (p q : Pattern) (h : Agree support p q) : d7136 p = d7136 q := by
  simp only [d7136, h 116 (by decide), agree7135 p q h, agree7128 p q h]
theorem nonnegative7136 (p : Pattern) : 0 ≤ d7136 p :=
  nonnegative_ite (p 116) (nonnegative7135 p) (nonnegative7128 p)
def d7137 (p : Pattern) : Int := if p 115 then d7136 p else d7134 p
theorem agree7137 (p q : Pattern) (h : Agree support p q) : d7137 p = d7137 q := by
  simp only [d7137, h 115 (by decide), agree7136 p q h, agree7134 p q h]
theorem nonnegative7137 (p : Pattern) : 0 ≤ d7137 p :=
  nonnegative_ite (p 115) (nonnegative7136 p) (nonnegative7134 p)
def d7138 (p : Pattern) : Int := if p 71 then d7137 p else d7079 p
theorem agree7138 (p q : Pattern) (h : Agree support p q) : d7138 p = d7138 q := by
  simp only [d7138, h 71 (by decide), agree7137 p q h, agree7079 p q h]
theorem nonnegative7138 (p : Pattern) : 0 ≤ d7138 p :=
  nonnegative_ite (p 71) (nonnegative7137 p) (nonnegative7079 p)
def d7139 (p : Pattern) : Int := if p 49 then d7138 p else d7079 p
theorem agree7139 (p q : Pattern) (h : Agree support p q) : d7139 p = d7139 q := by
  simp only [d7139, h 49 (by decide), agree7138 p q h, agree7079 p q h]
theorem nonnegative7139 (p : Pattern) : 0 ≤ d7139 p :=
  nonnegative_ite (p 49) (nonnegative7138 p) (nonnegative7079 p)
def d7140 (p : Pattern) : Int := if p 182 then d12 p else d3079 p
theorem agree7140 (p q : Pattern) (h : Agree support p q) : d7140 p = d7140 q := by
  simp only [d7140, h 182 (by decide), agree12 p q h, agree3079 p q h]
theorem nonnegative7140 (p : Pattern) : 0 ≤ d7140 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3079 p)
def d7141 (p : Pattern) : Int := if p 163 then d7140 p else d7048 p
theorem agree7141 (p q : Pattern) (h : Agree support p q) : d7141 p = d7141 q := by
  simp only [d7141, h 163 (by decide), agree7140 p q h, agree7048 p q h]
theorem nonnegative7141 (p : Pattern) : 0 ≤ d7141 p :=
  nonnegative_ite (p 163) (nonnegative7140 p) (nonnegative7048 p)
def d7142 (p : Pattern) : Int := if p 162 then d7141 p else d7048 p
theorem agree7142 (p q : Pattern) (h : Agree support p q) : d7142 p = d7142 q := by
  simp only [d7142, h 162 (by decide), agree7141 p q h, agree7048 p q h]
theorem nonnegative7142 (p : Pattern) : 0 ≤ d7142 p :=
  nonnegative_ite (p 162) (nonnegative7141 p) (nonnegative7048 p)
def d7143 (p : Pattern) : Int := if p 162 then d7019 p else d7141 p
theorem agree7143 (p q : Pattern) (h : Agree support p q) : d7143 p = d7143 q := by
  simp only [d7143, h 162 (by decide), agree7019 p q h, agree7141 p q h]
theorem nonnegative7143 (p : Pattern) : 0 ≤ d7143 p :=
  nonnegative_ite (p 162) (nonnegative7019 p) (nonnegative7141 p)
def d7144 (p : Pattern) : Int := if p 161 then d7143 p else d7142 p
theorem agree7144 (p q : Pattern) (h : Agree support p q) : d7144 p = d7144 q := by
  simp only [d7144, h 161 (by decide), agree7143 p q h, agree7142 p q h]
theorem nonnegative7144 (p : Pattern) : 0 ≤ d7144 p :=
  nonnegative_ite (p 161) (nonnegative7143 p) (nonnegative7142 p)
def d7145 (p : Pattern) : Int := if p 162 then d7054 p else d7039 p
theorem agree7145 (p q : Pattern) (h : Agree support p q) : d7145 p = d7145 q := by
  simp only [d7145, h 162 (by decide), agree7054 p q h, agree7039 p q h]
theorem nonnegative7145 (p : Pattern) : 0 ≤ d7145 p :=
  nonnegative_ite (p 162) (nonnegative7054 p) (nonnegative7039 p)
def d7146 (p : Pattern) : Int := if p 161 then d7055 p else d7145 p
theorem agree7146 (p q : Pattern) (h : Agree support p q) : d7146 p = d7146 q := by
  simp only [d7146, h 161 (by decide), agree7055 p q h, agree7145 p q h]
theorem nonnegative7146 (p : Pattern) : 0 ≤ d7146 p :=
  nonnegative_ite (p 161) (nonnegative7055 p) (nonnegative7145 p)
def d7147 (p : Pattern) : Int := if p 160 then d7146 p else d7144 p
theorem agree7147 (p q : Pattern) (h : Agree support p q) : d7147 p = d7147 q := by
  simp only [d7147, h 160 (by decide), agree7146 p q h, agree7144 p q h]
theorem nonnegative7147 (p : Pattern) : 0 ≤ d7147 p :=
  nonnegative_ite (p 160) (nonnegative7146 p) (nonnegative7144 p)
def d7148 (p : Pattern) : Int := if p 182 then d12 p else d3097 p
theorem agree7148 (p q : Pattern) (h : Agree support p q) : d7148 p = d7148 q := by
  simp only [d7148, h 182 (by decide), agree12 p q h, agree3097 p q h]
theorem nonnegative7148 (p : Pattern) : 0 ≤ d7148 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3097 p)
def d7149 (p : Pattern) : Int := if p 163 then d7148 p else d7048 p
theorem agree7149 (p q : Pattern) (h : Agree support p q) : d7149 p = d7149 q := by
  simp only [d7149, h 163 (by decide), agree7148 p q h, agree7048 p q h]
theorem nonnegative7149 (p : Pattern) : 0 ≤ d7149 p :=
  nonnegative_ite (p 163) (nonnegative7148 p) (nonnegative7048 p)
def d7150 (p : Pattern) : Int := if p 163 then d7018 p else d7140 p
theorem agree7150 (p q : Pattern) (h : Agree support p q) : d7150 p = d7150 q := by
  simp only [d7150, h 163 (by decide), agree7018 p q h, agree7140 p q h]
theorem nonnegative7150 (p : Pattern) : 0 ≤ d7150 p :=
  nonnegative_ite (p 163) (nonnegative7018 p) (nonnegative7140 p)
def d7151 (p : Pattern) : Int := if p 162 then d7150 p else d7149 p
theorem agree7151 (p q : Pattern) (h : Agree support p q) : d7151 p = d7151 q := by
  simp only [d7151, h 162 (by decide), agree7150 p q h, agree7149 p q h]
theorem nonnegative7151 (p : Pattern) : 0 ≤ d7151 p :=
  nonnegative_ite (p 162) (nonnegative7150 p) (nonnegative7149 p)
def d7152 (p : Pattern) : Int := if p 163 then d7033 p else d7140 p
theorem agree7152 (p q : Pattern) (h : Agree support p q) : d7152 p = d7152 q := by
  simp only [d7152, h 163 (by decide), agree7033 p q h, agree7140 p q h]
theorem nonnegative7152 (p : Pattern) : 0 ≤ d7152 p :=
  nonnegative_ite (p 163) (nonnegative7033 p) (nonnegative7140 p)
def d7153 (p : Pattern) : Int := if p 162 then d7036 p else d7152 p
theorem agree7153 (p q : Pattern) (h : Agree support p q) : d7153 p = d7153 q := by
  simp only [d7153, h 162 (by decide), agree7036 p q h, agree7152 p q h]
theorem nonnegative7153 (p : Pattern) : 0 ≤ d7153 p :=
  nonnegative_ite (p 162) (nonnegative7036 p) (nonnegative7152 p)
def d7154 (p : Pattern) : Int := if p 161 then d7153 p else d7151 p
theorem agree7154 (p q : Pattern) (h : Agree support p q) : d7154 p = d7154 q := by
  simp only [d7154, h 161 (by decide), agree7153 p q h, agree7151 p q h]
theorem nonnegative7154 (p : Pattern) : 0 ≤ d7154 p :=
  nonnegative_ite (p 161) (nonnegative7153 p) (nonnegative7151 p)
def d7155 (p : Pattern) : Int := if p 163 then d7023 p else d7039 p
theorem agree7155 (p q : Pattern) (h : Agree support p q) : d7155 p = d7155 q := by
  simp only [d7155, h 163 (by decide), agree7023 p q h, agree7039 p q h]
theorem nonnegative7155 (p : Pattern) : 0 ≤ d7155 p :=
  nonnegative_ite (p 163) (nonnegative7023 p) (nonnegative7039 p)
def d7156 (p : Pattern) : Int := if p 163 then d7035 p else d7053 p
theorem agree7156 (p q : Pattern) (h : Agree support p q) : d7156 p = d7156 q := by
  simp only [d7156, h 163 (by decide), agree7035 p q h, agree7053 p q h]
theorem nonnegative7156 (p : Pattern) : 0 ≤ d7156 p :=
  nonnegative_ite (p 163) (nonnegative7035 p) (nonnegative7053 p)
def d7157 (p : Pattern) : Int := if p 162 then d7156 p else d7155 p
theorem agree7157 (p q : Pattern) (h : Agree support p q) : d7157 p = d7157 q := by
  simp only [d7157, h 162 (by decide), agree7156 p q h, agree7155 p q h]
theorem nonnegative7157 (p : Pattern) : 0 ≤ d7157 p :=
  nonnegative_ite (p 162) (nonnegative7156 p) (nonnegative7155 p)
def d7158 (p : Pattern) : Int := if p 161 then d7062 p else d7157 p
theorem agree7158 (p q : Pattern) (h : Agree support p q) : d7158 p = d7158 q := by
  simp only [d7158, h 161 (by decide), agree7062 p q h, agree7157 p q h]
theorem nonnegative7158 (p : Pattern) : 0 ≤ d7158 p :=
  nonnegative_ite (p 161) (nonnegative7062 p) (nonnegative7157 p)
def d7159 (p : Pattern) : Int := if p 160 then d7158 p else d7154 p
theorem agree7159 (p q : Pattern) (h : Agree support p q) : d7159 p = d7159 q := by
  simp only [d7159, h 160 (by decide), agree7158 p q h, agree7154 p q h]
theorem nonnegative7159 (p : Pattern) : 0 ≤ d7159 p :=
  nonnegative_ite (p 160) (nonnegative7158 p) (nonnegative7154 p)
def d7160 (p : Pattern) : Int := if p 141 then d7159 p else d7147 p
theorem agree7160 (p q : Pattern) (h : Agree support p q) : d7160 p = d7160 q := by
  simp only [d7160, h 141 (by decide), agree7159 p q h, agree7147 p q h]
theorem nonnegative7160 (p : Pattern) : 0 ≤ d7160 p :=
  nonnegative_ite (p 141) (nonnegative7159 p) (nonnegative7147 p)
def d7161 (p : Pattern) : Int := if p 182 then d12 p else d1781 p
theorem agree7161 (p q : Pattern) (h : Agree support p q) : d7161 p = d7161 q := by
  simp only [d7161, h 182 (by decide), agree12 p q h, agree1781 p q h]
theorem nonnegative7161 (p : Pattern) : 0 ≤ d7161 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1781 p)
def d7162 (p : Pattern) : Int := if p 163 then d7022 p else d7161 p
theorem agree7162 (p q : Pattern) (h : Agree support p q) : d7162 p = d7162 q := by
  simp only [d7162, h 163 (by decide), agree7022 p q h, agree7161 p q h]
theorem nonnegative7162 (p : Pattern) : 0 ≤ d7162 p :=
  nonnegative_ite (p 163) (nonnegative7022 p) (nonnegative7161 p)
def d7163 (p : Pattern) : Int := if p 162 then d7054 p else d7162 p
theorem agree7163 (p q : Pattern) (h : Agree support p q) : d7163 p = d7163 q := by
  simp only [d7163, h 162 (by decide), agree7054 p q h, agree7162 p q h]
theorem nonnegative7163 (p : Pattern) : 0 ≤ d7163 p :=
  nonnegative_ite (p 162) (nonnegative7054 p) (nonnegative7162 p)
def d7164 (p : Pattern) : Int := if p 161 then d7055 p else d7163 p
theorem agree7164 (p q : Pattern) (h : Agree support p q) : d7164 p = d7164 q := by
  simp only [d7164, h 161 (by decide), agree7055 p q h, agree7163 p q h]
theorem nonnegative7164 (p : Pattern) : 0 ≤ d7164 p :=
  nonnegative_ite (p 161) (nonnegative7055 p) (nonnegative7163 p)
def d7165 (p : Pattern) : Int := if p 182 then d12 p else d2061 p
theorem agree7165 (p q : Pattern) (h : Agree support p q) : d7165 p = d7165 q := by
  simp only [d7165, h 182 (by decide), agree12 p q h, agree2061 p q h]
theorem nonnegative7165 (p : Pattern) : 0 ≤ d7165 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2061 p)
def d7166 (p : Pattern) : Int := if p 163 then d7165 p else d7023 p
theorem agree7166 (p q : Pattern) (h : Agree support p q) : d7166 p = d7166 q := by
  simp only [d7166, h 163 (by decide), agree7165 p q h, agree7023 p q h]
theorem nonnegative7166 (p : Pattern) : 0 ≤ d7166 p :=
  nonnegative_ite (p 163) (nonnegative7165 p) (nonnegative7023 p)
def d7167 (p : Pattern) : Int := if p 162 then d12 p else d7166 p
theorem agree7167 (p q : Pattern) (h : Agree support p q) : d7167 p = d7167 q := by
  simp only [d7167, h 162 (by decide), agree12 p q h, agree7166 p q h]
theorem nonnegative7167 (p : Pattern) : 0 ≤ d7167 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7166 p)
def d7168 (p : Pattern) : Int := if p 161 then d12 p else d7167 p
theorem agree7168 (p q : Pattern) (h : Agree support p q) : d7168 p = d7168 q := by
  simp only [d7168, h 161 (by decide), agree12 p q h, agree7167 p q h]
theorem nonnegative7168 (p : Pattern) : 0 ≤ d7168 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7167 p)
def d7169 (p : Pattern) : Int := if p 160 then d7168 p else d7164 p
theorem agree7169 (p q : Pattern) (h : Agree support p q) : d7169 p = d7169 q := by
  simp only [d7169, h 160 (by decide), agree7168 p q h, agree7164 p q h]
theorem nonnegative7169 (p : Pattern) : 0 ≤ d7169 p :=
  nonnegative_ite (p 160) (nonnegative7168 p) (nonnegative7164 p)
def d7170 (p : Pattern) : Int := if p 163 then d7035 p else d7023 p
theorem agree7170 (p q : Pattern) (h : Agree support p q) : d7170 p = d7170 q := by
  simp only [d7170, h 163 (by decide), agree7035 p q h, agree7023 p q h]
theorem nonnegative7170 (p : Pattern) : 0 ≤ d7170 p :=
  nonnegative_ite (p 163) (nonnegative7035 p) (nonnegative7023 p)
def d7171 (p : Pattern) : Int := if p 162 then d7170 p else d7039 p
theorem agree7171 (p q : Pattern) (h : Agree support p q) : d7171 p = d7171 q := by
  simp only [d7171, h 162 (by decide), agree7170 p q h, agree7039 p q h]
theorem nonnegative7171 (p : Pattern) : 0 ≤ d7171 p :=
  nonnegative_ite (p 162) (nonnegative7170 p) (nonnegative7039 p)
def d7172 (p : Pattern) : Int := if p 161 then d7062 p else d7171 p
theorem agree7172 (p q : Pattern) (h : Agree support p q) : d7172 p = d7172 q := by
  simp only [d7172, h 161 (by decide), agree7062 p q h, agree7171 p q h]
theorem nonnegative7172 (p : Pattern) : 0 ≤ d7172 p :=
  nonnegative_ite (p 161) (nonnegative7062 p) (nonnegative7171 p)
def d7173 (p : Pattern) : Int := if p 163 then d12 p else d7165 p
theorem agree7173 (p q : Pattern) (h : Agree support p q) : d7173 p = d7173 q := by
  simp only [d7173, h 163 (by decide), agree12 p q h, agree7165 p q h]
theorem nonnegative7173 (p : Pattern) : 0 ≤ d7173 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7165 p)
def d7174 (p : Pattern) : Int := if p 162 then d12 p else d7173 p
theorem agree7174 (p q : Pattern) (h : Agree support p q) : d7174 p = d7174 q := by
  simp only [d7174, h 162 (by decide), agree12 p q h, agree7173 p q h]
theorem nonnegative7174 (p : Pattern) : 0 ≤ d7174 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7173 p)
def d7175 (p : Pattern) : Int := if p 161 then d12 p else d7174 p
theorem agree7175 (p q : Pattern) (h : Agree support p q) : d7175 p = d7175 q := by
  simp only [d7175, h 161 (by decide), agree12 p q h, agree7174 p q h]
theorem nonnegative7175 (p : Pattern) : 0 ≤ d7175 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7174 p)
def d7176 (p : Pattern) : Int := if p 160 then d7175 p else d7172 p
theorem agree7176 (p q : Pattern) (h : Agree support p q) : d7176 p = d7176 q := by
  simp only [d7176, h 160 (by decide), agree7175 p q h, agree7172 p q h]
theorem nonnegative7176 (p : Pattern) : 0 ≤ d7176 p :=
  nonnegative_ite (p 160) (nonnegative7175 p) (nonnegative7172 p)
def d7177 (p : Pattern) : Int := if p 141 then d7176 p else d7169 p
theorem agree7177 (p q : Pattern) (h : Agree support p q) : d7177 p = d7177 q := by
  simp only [d7177, h 141 (by decide), agree7176 p q h, agree7169 p q h]
theorem nonnegative7177 (p : Pattern) : 0 ≤ d7177 p :=
  nonnegative_ite (p 141) (nonnegative7176 p) (nonnegative7169 p)
def d7178 (p : Pattern) : Int := if p 138 then d7177 p else d7160 p
theorem agree7178 (p q : Pattern) (h : Agree support p q) : d7178 p = d7178 q := by
  simp only [d7178, h 138 (by decide), agree7177 p q h, agree7160 p q h]
theorem nonnegative7178 (p : Pattern) : 0 ≤ d7178 p :=
  nonnegative_ite (p 138) (nonnegative7177 p) (nonnegative7160 p)
def d7179 (p : Pattern) : Int := if p 138 then d12 p else d7177 p
theorem agree7179 (p q : Pattern) (h : Agree support p q) : d7179 p = d7179 q := by
  simp only [d7179, h 138 (by decide), agree12 p q h, agree7177 p q h]
theorem nonnegative7179 (p : Pattern) : 0 ≤ d7179 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7177 p)
def d7180 (p : Pattern) : Int := if p 116 then d7179 p else d7178 p
theorem agree7180 (p q : Pattern) (h : Agree support p q) : d7180 p = d7180 q := by
  simp only [d7180, h 116 (by decide), agree7179 p q h, agree7178 p q h]
theorem nonnegative7180 (p : Pattern) : 0 ≤ d7180 p :=
  nonnegative_ite (p 116) (nonnegative7179 p) (nonnegative7178 p)
def d7181 (p : Pattern) : Int := if p 115 then d7180 p else d7076 p
theorem agree7181 (p q : Pattern) (h : Agree support p q) : d7181 p = d7181 q := by
  simp only [d7181, h 115 (by decide), agree7180 p q h, agree7076 p q h]
theorem nonnegative7181 (p : Pattern) : 0 ≤ d7181 p :=
  nonnegative_ite (p 115) (nonnegative7180 p) (nonnegative7076 p)
def d7182 (p : Pattern) : Int := if p 71 then d7181 p else d7079 p
theorem agree7182 (p q : Pattern) (h : Agree support p q) : d7182 p = d7182 q := by
  simp only [d7182, h 71 (by decide), agree7181 p q h, agree7079 p q h]
theorem nonnegative7182 (p : Pattern) : 0 ≤ d7182 p :=
  nonnegative_ite (p 71) (nonnegative7181 p) (nonnegative7079 p)
def d7183 (p : Pattern) : Int := if p 163 then d12 p else d7081 p
theorem agree7183 (p q : Pattern) (h : Agree support p q) : d7183 p = d7183 q := by
  simp only [d7183, h 163 (by decide), agree12 p q h, agree7081 p q h]
theorem nonnegative7183 (p : Pattern) : 0 ≤ d7183 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7081 p)
def d7184 (p : Pattern) : Int := if p 162 then d7183 p else d7095 p
theorem agree7184 (p q : Pattern) (h : Agree support p q) : d7184 p = d7184 q := by
  simp only [d7184, h 162 (by decide), agree7183 p q h, agree7095 p q h]
theorem nonnegative7184 (p : Pattern) : 0 ≤ d7184 p :=
  nonnegative_ite (p 162) (nonnegative7183 p) (nonnegative7095 p)
def d7185 (p : Pattern) : Int := if p 162 then d12 p else d7183 p
theorem agree7185 (p q : Pattern) (h : Agree support p q) : d7185 p = d7185 q := by
  simp only [d7185, h 162 (by decide), agree12 p q h, agree7183 p q h]
theorem nonnegative7185 (p : Pattern) : 0 ≤ d7185 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7183 p)
def d7186 (p : Pattern) : Int := if p 161 then d7185 p else d7184 p
theorem agree7186 (p q : Pattern) (h : Agree support p q) : d7186 p = d7186 q := by
  simp only [d7186, h 161 (by decide), agree7185 p q h, agree7184 p q h]
theorem nonnegative7186 (p : Pattern) : 0 ≤ d7186 p :=
  nonnegative_ite (p 161) (nonnegative7185 p) (nonnegative7184 p)
def d7187 (p : Pattern) : Int := if p 163 then d12 p else d7088 p
theorem agree7187 (p q : Pattern) (h : Agree support p q) : d7187 p = d7187 q := by
  simp only [d7187, h 163 (by decide), agree12 p q h, agree7088 p q h]
theorem nonnegative7187 (p : Pattern) : 0 ≤ d7187 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7088 p)
def d7188 (p : Pattern) : Int := if p 162 then d7187 p else d7102 p
theorem agree7188 (p q : Pattern) (h : Agree support p q) : d7188 p = d7188 q := by
  simp only [d7188, h 162 (by decide), agree7187 p q h, agree7102 p q h]
theorem nonnegative7188 (p : Pattern) : 0 ≤ d7188 p :=
  nonnegative_ite (p 162) (nonnegative7187 p) (nonnegative7102 p)
def d7189 (p : Pattern) : Int := if p 162 then d12 p else d7187 p
theorem agree7189 (p q : Pattern) (h : Agree support p q) : d7189 p = d7189 q := by
  simp only [d7189, h 162 (by decide), agree12 p q h, agree7187 p q h]
theorem nonnegative7189 (p : Pattern) : 0 ≤ d7189 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7187 p)
def d7190 (p : Pattern) : Int := if p 161 then d7189 p else d7188 p
theorem agree7190 (p q : Pattern) (h : Agree support p q) : d7190 p = d7190 q := by
  simp only [d7190, h 161 (by decide), agree7189 p q h, agree7188 p q h]
theorem nonnegative7190 (p : Pattern) : 0 ≤ d7190 p :=
  nonnegative_ite (p 161) (nonnegative7189 p) (nonnegative7188 p)
def d7191 (p : Pattern) : Int := if p 160 then d7190 p else d7186 p
theorem agree7191 (p q : Pattern) (h : Agree support p q) : d7191 p = d7191 q := by
  simp only [d7191, h 160 (by decide), agree7190 p q h, agree7186 p q h]
theorem nonnegative7191 (p : Pattern) : 0 ≤ d7191 p :=
  nonnegative_ite (p 160) (nonnegative7190 p) (nonnegative7186 p)
def d7192 (p : Pattern) : Int := if p 141 then d7191 p else d7093 p
theorem agree7192 (p q : Pattern) (h : Agree support p q) : d7192 p = d7192 q := by
  simp only [d7192, h 141 (by decide), agree7191 p q h, agree7093 p q h]
theorem nonnegative7192 (p : Pattern) : 0 ≤ d7192 p :=
  nonnegative_ite (p 141) (nonnegative7191 p) (nonnegative7093 p)
def d7193 (p : Pattern) : Int := if p 162 then d7187 p else d7120 p
theorem agree7193 (p q : Pattern) (h : Agree support p q) : d7193 p = d7193 q := by
  simp only [d7193, h 162 (by decide), agree7187 p q h, agree7120 p q h]
theorem nonnegative7193 (p : Pattern) : 0 ≤ d7193 p :=
  nonnegative_ite (p 162) (nonnegative7187 p) (nonnegative7120 p)
def d7194 (p : Pattern) : Int := if p 161 then d7189 p else d7193 p
theorem agree7194 (p q : Pattern) (h : Agree support p q) : d7194 p = d7194 q := by
  simp only [d7194, h 161 (by decide), agree7189 p q h, agree7193 p q h]
theorem nonnegative7194 (p : Pattern) : 0 ≤ d7194 p :=
  nonnegative_ite (p 161) (nonnegative7189 p) (nonnegative7193 p)
def d7195 (p : Pattern) : Int := if p 160 then d7125 p else d7194 p
theorem agree7195 (p q : Pattern) (h : Agree support p q) : d7195 p = d7195 q := by
  simp only [d7195, h 160 (by decide), agree7125 p q h, agree7194 p q h]
theorem nonnegative7195 (p : Pattern) : 0 ≤ d7195 p :=
  nonnegative_ite (p 160) (nonnegative7125 p) (nonnegative7194 p)
def d7196 (p : Pattern) : Int := if p 141 then d7195 p else d7119 p
theorem agree7196 (p q : Pattern) (h : Agree support p q) : d7196 p = d7196 q := by
  simp only [d7196, h 141 (by decide), agree7195 p q h, agree7119 p q h]
theorem nonnegative7196 (p : Pattern) : 0 ≤ d7196 p :=
  nonnegative_ite (p 141) (nonnegative7195 p) (nonnegative7119 p)
def d7197 (p : Pattern) : Int := if p 138 then d7196 p else d7192 p
theorem agree7197 (p q : Pattern) (h : Agree support p q) : d7197 p = d7197 q := by
  simp only [d7197, h 138 (by decide), agree7196 p q h, agree7192 p q h]
theorem nonnegative7197 (p : Pattern) : 0 ≤ d7197 p :=
  nonnegative_ite (p 138) (nonnegative7196 p) (nonnegative7192 p)
def d7198 (p : Pattern) : Int := if p 138 then d7132 p else d7196 p
theorem agree7198 (p q : Pattern) (h : Agree support p q) : d7198 p = d7198 q := by
  simp only [d7198, h 138 (by decide), agree7132 p q h, agree7196 p q h]
theorem nonnegative7198 (p : Pattern) : 0 ≤ d7198 p :=
  nonnegative_ite (p 138) (nonnegative7132 p) (nonnegative7196 p)
def d7199 (p : Pattern) : Int := if p 116 then d7198 p else d7197 p
theorem agree7199 (p q : Pattern) (h : Agree support p q) : d7199 p = d7199 q := by
  simp only [d7199, h 116 (by decide), agree7198 p q h, agree7197 p q h]
theorem nonnegative7199 (p : Pattern) : 0 ≤ d7199 p :=
  nonnegative_ite (p 116) (nonnegative7198 p) (nonnegative7197 p)
end NetHack.Sokoban22Refined85
