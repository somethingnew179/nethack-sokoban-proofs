/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions58
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub7080 (p : Pattern) : d254 (change p 10000 (some 182)) = d4288 p := by
  change (if p 163 then d26 (change p 10000 (some 182)) else d109 (change p 10000 (some 182))) = d4288 p
  rw [sub6843, sub6932]
  rfl
theorem sub7081 (p : Pattern) : d255 (change p 10000 (some 182)) = d4289 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d254 (change p 10000 (some 182))) = d4289 p
  rw [sub6827, sub7080]
  rfl
theorem sub7082 (p : Pattern) : d256 (change p 10000 (some 182)) = d4290 p := by
  change (if p 161 then d255 (change p 10000 (some 182)) else d253 (change p 10000 (some 182))) = d4290 p
  rw [sub7081, sub7079]
  rfl
theorem sub7083 (p : Pattern) : d257 (change p 10000 (some 182)) = d4956 p := by
  change (if p 163 then d62 (change p 10000 (some 182)) else d148 (change p 10000 (some 182))) = d4956 p
  rw [sub6883, sub6973]
  rfl
theorem sub7084 (p : Pattern) : d258 (change p 10000 (some 182)) = d4957 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d257 (change p 10000 (some 182))) = d4957 p
  rw [sub6827, sub7083]
  rfl
theorem sub7085 (p : Pattern) : d259 (change p 10000 (some 182)) = d4958 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d258 (change p 10000 (some 182))) = d4958 p
  rw [sub6827, sub7084]
  rfl
theorem sub7086 (p : Pattern) : d260 (change p 10000 (some 182)) = d4959 p := by
  change (if p 160 then d259 (change p 10000 (some 182)) else d256 (change p 10000 (some 182))) = d4959 p
  rw [sub7085, sub7082]
  rfl
theorem sub7087 (p : Pattern) : d261 (change p 10000 (some 182)) = d4960 p := by
  change (if p 141 then d249 (change p 10000 (some 182)) else d260 (change p 10000 (some 182))) = d4960 p
  rw [sub7075, sub7086]
  rfl
theorem sub7088 (p : Pattern) : d262 (change p 10000 (some 182)) = d4961 p := by
  change (if p 138 then d12 (change p 10000 (some 182)) else d261 (change p 10000 (some 182))) = d4961 p
  rw [sub6827, sub7087]
  rfl
theorem sub7089 (p : Pattern) : d263 (change p 10000 (some 182)) = d4962 p := by
  change (if p 116 then d262 (change p 10000 (some 182)) else d251 (change p 10000 (some 182))) = d4962 p
  rw [sub7088, sub7077]
  rfl
theorem sub7090 (p : Pattern) : d264 (change p 10000 (some 182)) = d4963 p := by
  change (if p 115 then d263 (change p 10000 (some 182)) else d225 (change p 10000 (some 182))) = d4963 p
  rw [sub7089, sub7051]
  rfl
theorem sub7091 (p : Pattern) : d265 (change p 10000 (some 182)) = d4964 p := by
  change (if p 71 then d264 (change p 10000 (some 182)) else d101 (change p 10000 (some 182))) = d4964 p
  rw [sub7090, sub6922]
  rfl
theorem sub7092 (p : Pattern) : d266 (change p 10000 (some 182)) = d4965 p := by
  change (if p 49 then d265 (change p 10000 (some 182)) else d210 (change p 10000 (some 182))) = d4965 p
  rw [sub7091, sub7036]
  rfl
theorem sub7093 (p : Pattern) : d267 (change p 10000 (some 182)) = d4966 p := by
  change (if p 48 then d266 (change p 10000 (some 182)) else d169 (change p 10000 (some 182))) = d4966 p
  rw [sub7092, sub6994]
  rfl
theorem sub7094 (p : Pattern) : d0 (change p 160 (some 138)) = d0 p := by
  rfl
theorem sub7095 (p : Pattern) : d12 (change p 160 (some 138)) = d12 p := by
  rfl
theorem sub7096 (p : Pattern) : d13 (change p 160 (some 138)) = d13 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d0 (change p 160 (some 138))) = d13 p
  rw [sub7095, sub7094]
  rfl
theorem sub7097 (p : Pattern) : d14 (change p 160 (some 138)) = d14 p := by
  change (if p 246 then d13 (change p 160 (some 138)) else d0 (change p 160 (some 138))) = d14 p
  rw [sub7096, sub7094]
  rfl
theorem sub7098 (p : Pattern) : d15 (change p 160 (some 138)) = d15 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d14 (change p 160 (some 138))) = d15 p
  rw [sub7095, sub7097]
  rfl
theorem sub7099 (p : Pattern) : d16 (change p 160 (some 138)) = d16 p := by
  change (if p 182 then d15 (change p 160 (some 138)) else d14 (change p 160 (some 138))) = d16 p
  rw [sub7098, sub7097]
  rfl
theorem sub7100 (p : Pattern) : d4 (change p 160 (some 138)) = d4 p := by
  rfl
theorem sub7101 (p : Pattern) : d17 (change p 160 (some 138)) = d17 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d4 (change p 160 (some 138))) = d17 p
  rw [sub7095, sub7100]
  rfl
theorem sub7102 (p : Pattern) : d18 (change p 160 (some 138)) = d18 p := by
  change (if p 246 then d17 (change p 160 (some 138)) else d4 (change p 160 (some 138))) = d18 p
  rw [sub7101, sub7100]
  rfl
theorem sub7103 (p : Pattern) : d19 (change p 160 (some 138)) = d19 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d18 (change p 160 (some 138))) = d19 p
  rw [sub7095, sub7102]
  rfl
theorem sub7104 (p : Pattern) : d20 (change p 160 (some 138)) = d20 p := by
  change (if p 182 then d19 (change p 160 (some 138)) else d18 (change p 160 (some 138))) = d20 p
  rw [sub7103, sub7102]
  rfl
theorem sub7105 (p : Pattern) : d21 (change p 160 (some 138)) = d21 p := by
  change (if p 163 then d20 (change p 160 (some 138)) else d16 (change p 160 (some 138))) = d21 p
  rw [sub7104, sub7099]
  rfl
theorem sub7106 (p : Pattern) : d22 (change p 160 (some 138)) = d22 p := by
  change (if p 162 then d21 (change p 160 (some 138)) else d16 (change p 160 (some 138))) = d22 p
  rw [sub7105, sub7099]
  rfl
theorem sub7107 (p : Pattern) : d9 (change p 160 (some 138)) = d9 p := by
  rfl
theorem sub7108 (p : Pattern) : d23 (change p 160 (some 138)) = d23 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d9 (change p 160 (some 138))) = d23 p
  rw [sub7095, sub7107]
  rfl
theorem sub7109 (p : Pattern) : d24 (change p 160 (some 138)) = d24 p := by
  change (if p 246 then d23 (change p 160 (some 138)) else d9 (change p 160 (some 138))) = d24 p
  rw [sub7108, sub7107]
  rfl
theorem sub7110 (p : Pattern) : d25 (change p 160 (some 138)) = d25 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d24 (change p 160 (some 138))) = d25 p
  rw [sub7095, sub7109]
  rfl
theorem sub7111 (p : Pattern) : d26 (change p 160 (some 138)) = d26 p := by
  change (if p 182 then d25 (change p 160 (some 138)) else d24 (change p 160 (some 138))) = d26 p
  rw [sub7110, sub7109]
  rfl
theorem sub7112 (p : Pattern) : d27 (change p 160 (some 138)) = d27 p := by
  change (if p 163 then d12 (change p 160 (some 138)) else d26 (change p 160 (some 138))) = d27 p
  rw [sub7095, sub7111]
  rfl
theorem sub7113 (p : Pattern) : d28 (change p 160 (some 138)) = d28 p := by
  change (if p 162 then d27 (change p 160 (some 138)) else d21 (change p 160 (some 138))) = d28 p
  rw [sub7112, sub7105]
  rfl
theorem sub7114 (p : Pattern) : d29 (change p 160 (some 138)) = d29 p := by
  change (if p 161 then d28 (change p 160 (some 138)) else d22 (change p 160 (some 138))) = d29 p
  rw [sub7113, sub7106]
  rfl
theorem sub7115 (p : Pattern) : d713 (change p 160 (some 138)) = d29 p := by
  change d29 (change p 160 (some 138)) = d29 p
  exact sub7114 p
theorem sub7116 (p : Pattern) : d2 (change p 160 (some 138)) = d2 p := by
  rfl
theorem sub7117 (p : Pattern) : d30 (change p 160 (some 138)) = d30 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d2 (change p 160 (some 138))) = d30 p
  rw [sub7095, sub7116]
  rfl
theorem sub7118 (p : Pattern) : d31 (change p 160 (some 138)) = d31 p := by
  change (if p 246 then d30 (change p 160 (some 138)) else d2 (change p 160 (some 138))) = d31 p
  rw [sub7117, sub7116]
  rfl
theorem sub7119 (p : Pattern) : d32 (change p 160 (some 138)) = d32 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d31 (change p 160 (some 138))) = d32 p
  rw [sub7095, sub7118]
  rfl
theorem sub7120 (p : Pattern) : d53 (change p 160 (some 138)) = d53 p := by
  change (if p 182 then d32 (change p 160 (some 138)) else d31 (change p 160 (some 138))) = d53 p
  rw [sub7119, sub7118]
  rfl
theorem sub7121 (p : Pattern) : d54 (change p 160 (some 138)) = d54 p := by
  change (if p 163 then d53 (change p 160 (some 138)) else d16 (change p 160 (some 138))) = d54 p
  rw [sub7120, sub7099]
  rfl
theorem sub7122 (p : Pattern) : d55 (change p 160 (some 138)) = d55 p := by
  change (if p 163 then d26 (change p 160 (some 138)) else d20 (change p 160 (some 138))) = d55 p
  rw [sub7111, sub7104]
  rfl
theorem sub7123 (p : Pattern) : d56 (change p 160 (some 138)) = d56 p := by
  change (if p 162 then d55 (change p 160 (some 138)) else d54 (change p 160 (some 138))) = d56 p
  rw [sub7122, sub7121]
  rfl
theorem sub7124 (p : Pattern) : d10 (change p 160 (some 138)) = d10 p := by
  rfl
theorem sub7125 (p : Pattern) : d57 (change p 160 (some 138)) = d57 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d10 (change p 160 (some 138))) = d57 p
  rw [sub7095, sub7124]
  rfl
theorem sub7126 (p : Pattern) : d58 (change p 160 (some 138)) = d58 p := by
  change (if p 246 then d57 (change p 160 (some 138)) else d10 (change p 160 (some 138))) = d58 p
  rw [sub7125, sub7124]
  rfl
theorem sub7127 (p : Pattern) : d59 (change p 160 (some 138)) = d59 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d58 (change p 160 (some 138))) = d59 p
  rw [sub7095, sub7126]
  rfl
theorem sub7128 (p : Pattern) : d60 (change p 160 (some 138)) = d60 p := by
  change (if p 182 then d59 (change p 160 (some 138)) else d58 (change p 160 (some 138))) = d60 p
  rw [sub7127, sub7126]
  rfl
theorem sub7129 (p : Pattern) : d61 (change p 160 (some 138)) = d61 p := by
  change (if p 163 then d60 (change p 160 (some 138)) else d20 (change p 160 (some 138))) = d61 p
  rw [sub7128, sub7104]
  rfl
theorem sub7130 (p : Pattern) : d11 (change p 160 (some 138)) = d11 p := by
  rfl
theorem sub7131 (p : Pattern) : d39 (change p 160 (some 138)) = d39 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d11 (change p 160 (some 138))) = d39 p
  rw [sub7095, sub7130]
  rfl
theorem sub7132 (p : Pattern) : d40 (change p 160 (some 138)) = d40 p := by
  change (if p 246 then d39 (change p 160 (some 138)) else d11 (change p 160 (some 138))) = d40 p
  rw [sub7131, sub7130]
  rfl
theorem sub7133 (p : Pattern) : d41 (change p 160 (some 138)) = d41 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d40 (change p 160 (some 138))) = d41 p
  rw [sub7095, sub7132]
  rfl
theorem sub7134 (p : Pattern) : d62 (change p 160 (some 138)) = d62 p := by
  change (if p 182 then d41 (change p 160 (some 138)) else d40 (change p 160 (some 138))) = d62 p
  rw [sub7133, sub7132]
  rfl
theorem sub7135 (p : Pattern) : d63 (change p 160 (some 138)) = d63 p := by
  change (if p 163 then d12 (change p 160 (some 138)) else d62 (change p 160 (some 138))) = d63 p
  rw [sub7095, sub7134]
  rfl
theorem sub7136 (p : Pattern) : d64 (change p 160 (some 138)) = d64 p := by
  change (if p 162 then d63 (change p 160 (some 138)) else d61 (change p 160 (some 138))) = d64 p
  rw [sub7135, sub7129]
  rfl
theorem sub7137 (p : Pattern) : d65 (change p 160 (some 138)) = d65 p := by
  change (if p 161 then d64 (change p 160 (some 138)) else d56 (change p 160 (some 138))) = d65 p
  rw [sub7136, sub7123]
  rfl
theorem sub7138 (p : Pattern) : d714 (change p 160 (some 138)) = d65 p := by
  change d65 (change p 160 (some 138)) = d65 p
  exact sub7137 p
theorem sub7139 (p : Pattern) : d715 (change p 160 (some 138)) = d4729 p := by
  change (if p 141 then d714 (change p 160 (some 138)) else d713 (change p 160 (some 138))) = d4729 p
  rw [sub7138, sub7115]
  rfl
theorem sub7140 (p : Pattern) : d716 (change p 160 (some 138)) = d4729 p := by
  change d715 (change p 160 (some 138)) = d4729 p
  exact sub7139 p
theorem sub7141 (p : Pattern) : d89 (change p 160 (some 138)) = d89 p := by
  change (if p 163 then d62 (change p 160 (some 138)) else d26 (change p 160 (some 138))) = d89 p
  rw [sub7134, sub7111]
  rfl
theorem sub7142 (p : Pattern) : d90 (change p 160 (some 138)) = d90 p := by
  change (if p 162 then d63 (change p 160 (some 138)) else d89 (change p 160 (some 138))) = d90 p
  rw [sub7135, sub7141]
  rfl
theorem sub7143 (p : Pattern) : d91 (change p 160 (some 138)) = d91 p := by
  change (if p 162 then d12 (change p 160 (some 138)) else d63 (change p 160 (some 138))) = d91 p
  rw [sub7095, sub7135]
  rfl
theorem sub7144 (p : Pattern) : d92 (change p 160 (some 138)) = d92 p := by
  change (if p 161 then d91 (change p 160 (some 138)) else d90 (change p 160 (some 138))) = d92 p
  rw [sub7143, sub7142]
  rfl
theorem sub7145 (p : Pattern) : d719 (change p 160 (some 138)) = d92 p := by
  change d92 (change p 160 (some 138)) = d92 p
  exact sub7144 p
theorem sub7146 (p : Pattern) : d93 (change p 160 (some 138)) = d93 p := by
  change (if p 161 then d12 (change p 160 (some 138)) else d91 (change p 160 (some 138))) = d93 p
  rw [sub7095, sub7143]
  rfl
theorem sub7147 (p : Pattern) : d95 (change p 160 (some 138)) = d93 p := by
  change d93 (change p 160 (some 138)) = d93 p
  exact sub7146 p
theorem sub7148 (p : Pattern) : d720 (change p 160 (some 138)) = d4730 p := by
  change (if p 141 then d95 (change p 160 (some 138)) else d719 (change p 160 (some 138))) = d4730 p
  rw [sub7147, sub7145]
  rfl
theorem sub7149 (p : Pattern) : d721 (change p 160 (some 138)) = d4730 p := by
  change d720 (change p 160 (some 138)) = d4730 p
  exact sub7148 p
theorem sub7150 (p : Pattern) : d722 (change p 160 (some 138)) = d4968 p := by
  change (if p 116 then d721 (change p 160 (some 138)) else d716 (change p 160 (some 138))) = d4968 p
  rw [sub7149, sub7140]
  rfl
theorem sub7151 (p : Pattern) : d726 (change p 160 (some 138)) = d29 p := by
  change d29 (change p 160 (some 138)) = d29 p
  exact sub7114 p
theorem sub7152 (p : Pattern) : d727 (change p 160 (some 138)) = d4729 p := by
  change (if p 141 then d714 (change p 160 (some 138)) else d726 (change p 160 (some 138))) = d4729 p
  rw [sub7138, sub7151]
  rfl
theorem sub7153 (p : Pattern) : d728 (change p 160 (some 138)) = d4729 p := by
  change d727 (change p 160 (some 138)) = d4729 p
  exact sub7152 p
theorem sub7154 (p : Pattern) : d729 (change p 160 (some 138)) = d12 p := by
  change d12 (change p 160 (some 138)) = d12 p
  exact sub7095 p
theorem sub7155 (p : Pattern) : d730 (change p 160 (some 138)) = d4969 p := by
  change (if p 116 then d729 (change p 160 (some 138)) else d728 (change p 160 (some 138))) = d4969 p
  rw [sub7154, sub7153]
  rfl
theorem sub7156 (p : Pattern) : d731 (change p 160 (some 138)) = d4970 p := by
  change (if p 115 then d730 (change p 160 (some 138)) else d722 (change p 160 (some 138))) = d4970 p
  rw [sub7155, sub7150]
  rfl
theorem sub7157 (p : Pattern) : d735 (change p 160 (some 138)) = d4729 p := by
  change d727 (change p 160 (some 138)) = d4729 p
  exact sub7152 p
theorem sub7158 (p : Pattern) : d736 (change p 160 (some 138)) = d4730 p := by
  change d720 (change p 160 (some 138)) = d4730 p
  exact sub7148 p
theorem sub7159 (p : Pattern) : d737 (change p 160 (some 138)) = d4968 p := by
  change (if p 116 then d736 (change p 160 (some 138)) else d735 (change p 160 (some 138))) = d4968 p
  rw [sub7158, sub7157]
  rfl
theorem sub7160 (p : Pattern) : d738 (change p 160 (some 138)) = d4729 p := by
  change d727 (change p 160 (some 138)) = d4729 p
  exact sub7152 p
theorem sub7161 (p : Pattern) : d739 (change p 160 (some 138)) = d4969 p := by
  change (if p 116 then d729 (change p 160 (some 138)) else d738 (change p 160 (some 138))) = d4969 p
  rw [sub7154, sub7160]
  rfl
theorem sub7162 (p : Pattern) : d740 (change p 160 (some 138)) = d4970 p := by
  change (if p 115 then d739 (change p 160 (some 138)) else d737 (change p 160 (some 138))) = d4970 p
  rw [sub7161, sub7159]
  rfl
theorem sub7163 (p : Pattern) : d741 (change p 160 (some 138)) = d4970 p := by
  change (if p 71 then d740 (change p 160 (some 138)) else d731 (change p 160 (some 138))) = d4970 p
  rw [sub7162, sub7156]
  simp only [ite_self]
theorem sub7164 (p : Pattern) : d1 (change p 160 (some 138)) = d1 p := by
  rfl
theorem sub7165 (p : Pattern) : d102 (change p 160 (some 138)) = d102 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d1 (change p 160 (some 138))) = d102 p
  rw [sub7095, sub7164]
  rfl
theorem sub7166 (p : Pattern) : d103 (change p 160 (some 138)) = d103 p := by
  change (if p 246 then d102 (change p 160 (some 138)) else d1 (change p 160 (some 138))) = d103 p
  rw [sub7165, sub7164]
  rfl
theorem sub7167 (p : Pattern) : d104 (change p 160 (some 138)) = d104 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d103 (change p 160 (some 138))) = d104 p
  rw [sub7095, sub7166]
  rfl
theorem sub7168 (p : Pattern) : d105 (change p 160 (some 138)) = d105 p := by
  change (if p 182 then d104 (change p 160 (some 138)) else d103 (change p 160 (some 138))) = d105 p
  rw [sub7167, sub7166]
  rfl
theorem sub7169 (p : Pattern) : d5 (change p 160 (some 138)) = d5 p := by
  rfl
theorem sub7170 (p : Pattern) : d106 (change p 160 (some 138)) = d106 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d5 (change p 160 (some 138))) = d106 p
  rw [sub7095, sub7169]
  rfl
theorem sub7171 (p : Pattern) : d107 (change p 160 (some 138)) = d107 p := by
  change (if p 246 then d106 (change p 160 (some 138)) else d5 (change p 160 (some 138))) = d107 p
  rw [sub7170, sub7169]
  rfl
theorem sub7172 (p : Pattern) : d108 (change p 160 (some 138)) = d108 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d107 (change p 160 (some 138))) = d108 p
  rw [sub7095, sub7171]
  rfl
theorem sub7173 (p : Pattern) : d109 (change p 160 (some 138)) = d109 p := by
  change (if p 182 then d108 (change p 160 (some 138)) else d107 (change p 160 (some 138))) = d109 p
  rw [sub7172, sub7171]
  rfl
theorem sub7174 (p : Pattern) : d110 (change p 160 (some 138)) = d110 p := by
  change (if p 163 then d109 (change p 160 (some 138)) else d105 (change p 160 (some 138))) = d110 p
  rw [sub7173, sub7168]
  rfl
theorem sub7175 (p : Pattern) : d111 (change p 160 (some 138)) = d111 p := by
  change (if p 162 then d110 (change p 160 (some 138)) else d105 (change p 160 (some 138))) = d111 p
  rw [sub7174, sub7168]
  rfl
theorem sub7176 (p : Pattern) : d112 (change p 160 (some 138)) = d112 p := by
  change (if p 163 then d12 (change p 160 (some 138)) else d60 (change p 160 (some 138))) = d112 p
  rw [sub7095, sub7128]
  rfl
theorem sub7177 (p : Pattern) : d113 (change p 160 (some 138)) = d113 p := by
  change (if p 162 then d112 (change p 160 (some 138)) else d110 (change p 160 (some 138))) = d113 p
  rw [sub7176, sub7174]
  rfl
theorem sub7178 (p : Pattern) : d114 (change p 160 (some 138)) = d114 p := by
  change (if p 161 then d113 (change p 160 (some 138)) else d111 (change p 160 (some 138))) = d114 p
  rw [sub7177, sub7175]
  rfl
theorem sub7179 (p : Pattern) : d745 (change p 160 (some 138)) = d114 p := by
  change d114 (change p 160 (some 138)) = d114 p
  exact sub7178 p
theorem sub7180 (p : Pattern) : d3 (change p 160 (some 138)) = d3 p := by
  rfl
theorem sub7181 (p : Pattern) : d115 (change p 160 (some 138)) = d115 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d3 (change p 160 (some 138))) = d115 p
  rw [sub7095, sub7180]
  rfl
theorem sub7182 (p : Pattern) : d116 (change p 160 (some 138)) = d116 p := by
  change (if p 246 then d115 (change p 160 (some 138)) else d3 (change p 160 (some 138))) = d116 p
  rw [sub7181, sub7180]
  rfl
theorem sub7183 (p : Pattern) : d117 (change p 160 (some 138)) = d117 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d116 (change p 160 (some 138))) = d117 p
  rw [sub7095, sub7182]
  rfl
theorem sub7184 (p : Pattern) : d132 (change p 160 (some 138)) = d132 p := by
  change (if p 182 then d117 (change p 160 (some 138)) else d116 (change p 160 (some 138))) = d132 p
  rw [sub7183, sub7182]
  rfl
theorem sub7185 (p : Pattern) : d133 (change p 160 (some 138)) = d133 p := by
  change (if p 163 then d132 (change p 160 (some 138)) else d105 (change p 160 (some 138))) = d133 p
  rw [sub7184, sub7168]
  rfl
theorem sub7186 (p : Pattern) : d134 (change p 160 (some 138)) = d134 p := by
  change (if p 163 then d60 (change p 160 (some 138)) else d109 (change p 160 (some 138))) = d134 p
  rw [sub7128, sub7173]
  rfl
theorem sub7187 (p : Pattern) : d135 (change p 160 (some 138)) = d135 p := by
  change (if p 162 then d134 (change p 160 (some 138)) else d133 (change p 160 (some 138))) = d135 p
  rw [sub7186, sub7185]
  rfl
theorem sub7188 (p : Pattern) : d136 (change p 160 (some 138)) = d136 p := by
  change (if p 163 then d62 (change p 160 (some 138)) else d109 (change p 160 (some 138))) = d136 p
  rw [sub7134, sub7173]
  rfl
theorem sub7189 (p : Pattern) : d137 (change p 160 (some 138)) = d137 p := by
  change (if p 162 then d12 (change p 160 (some 138)) else d136 (change p 160 (some 138))) = d137 p
  rw [sub7095, sub7188]
  rfl
theorem sub7190 (p : Pattern) : d138 (change p 160 (some 138)) = d138 p := by
  change (if p 161 then d137 (change p 160 (some 138)) else d135 (change p 160 (some 138))) = d138 p
  rw [sub7189, sub7187]
  rfl
theorem sub7191 (p : Pattern) : d746 (change p 160 (some 138)) = d138 p := by
  change d138 (change p 160 (some 138)) = d138 p
  exact sub7190 p
theorem sub7192 (p : Pattern) : d747 (change p 160 (some 138)) = d4736 p := by
  change (if p 141 then d746 (change p 160 (some 138)) else d745 (change p 160 (some 138))) = d4736 p
  rw [sub7191, sub7179]
  rfl
theorem sub7193 (p : Pattern) : d748 (change p 160 (some 138)) = d4736 p := by
  change d747 (change p 160 (some 138)) = d4736 p
  exact sub7192 p
theorem sub7194 (p : Pattern) : d159 (change p 160 (some 138)) = d159 p := by
  change (if p 162 then d12 (change p 160 (some 138)) else d112 (change p 160 (some 138))) = d159 p
  rw [sub7095, sub7176]
  rfl
theorem sub7195 (p : Pattern) : d160 (change p 160 (some 138)) = d160 p := by
  change (if p 161 then d12 (change p 160 (some 138)) else d159 (change p 160 (some 138))) = d160 p
  rw [sub7095, sub7194]
  rfl
theorem sub7196 (p : Pattern) : d161 (change p 160 (some 138)) = d160 p := by
  change d160 (change p 160 (some 138)) = d160 p
  exact sub7195 p
theorem sub7197 (p : Pattern) : d162 (change p 160 (some 138)) = d4737 p := by
  change (if p 141 then d12 (change p 160 (some 138)) else d161 (change p 160 (some 138))) = d4737 p
  rw [sub7095, sub7196]
  rfl
theorem sub7198 (p : Pattern) : d751 (change p 160 (some 138)) = d4737 p := by
  change d162 (change p 160 (some 138)) = d4737 p
  exact sub7197 p
theorem sub7199 (p : Pattern) : d752 (change p 160 (some 138)) = d4971 p := by
  change (if p 116 then d751 (change p 160 (some 138)) else d748 (change p 160 (some 138))) = d4971 p
  rw [sub7198, sub7193]
  rfl
end NetHack.Sokoban22Refined85
