/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions75
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub9120 (p : Pattern) : d2068 (change p 10000 none) = d2068 p := by
  change (if p 247 then d10 (change p 10000 none) else d2 (change p 10000 none)) = d2068 p
  rw [sub51, sub21]
  rfl
theorem sub9121 (p : Pattern) : d2069 (change p 10000 none) = d2069 p := by
  change (if p 246 then d57 (change p 10000 none) else d2068 (change p 10000 none)) = d2069 p
  rw [sub52, sub9120]
  rfl
theorem sub9122 (p : Pattern) : d2070 (change p 10000 none) = d2070 p := by
  change (if p 225 then d2069 (change p 10000 none) else d1714 (change p 10000 none)) = d2070 p
  rw [sub9121, sub8783]
  rfl
theorem sub9123 (p : Pattern) : d2071 (change p 10000 none) = d2071 p := by
  change (if p 224 then d2070 (change p 10000 none) else d1712 (change p 10000 none)) = d2071 p
  rw [sub9122, sub8781]
  rfl
theorem sub9124 (p : Pattern) : d2072 (change p 10000 none) = d2072 p := by
  change (if p 204 then d12 (change p 10000 none) else d2071 (change p 10000 none)) = d2072 p
  rw [sub1, sub9123]
  rfl
theorem sub9125 (p : Pattern) : d3126 (change p 10000 none) = d3126 p := by
  change (if p 182 then d2072 (change p 10000 none) else d2935 (change p 10000 none)) = d3126 p
  rw [sub9124, sub8843]
  rfl
theorem sub9126 (p : Pattern) : d3127 (change p 10000 none) = d3127 p := by
  change (if p 163 then d2961 (change p 10000 none) else d3126 (change p 10000 none)) = d3127 p
  rw [sub8884, sub9125]
  rfl
theorem sub9127 (p : Pattern) : d3128 (change p 10000 none) = d3128 p := by
  change (if p 163 then d2931 (change p 10000 none) else d2954 (change p 10000 none)) = d3128 p
  rw [sub8839, sub8876]
  rfl
theorem sub9128 (p : Pattern) : d3129 (change p 10000 none) = d3129 p := by
  change (if p 162 then d3128 (change p 10000 none) else d3127 (change p 10000 none)) = d3129 p
  rw [sub9127, sub9126]
  rfl
theorem sub9129 (p : Pattern) : d3130 (change p 10000 none) = d3130 p := by
  change (if p 161 then d2975 (change p 10000 none) else d3129 (change p 10000 none)) = d3130 p
  rw [sub8898, sub9128]
  rfl
theorem sub9130 (p : Pattern) : d3131 (change p 10000 none) = d3131 p := by
  change (if p 163 then d12 (change p 10000 none) else d3121 (change p 10000 none)) = d3131 p
  rw [sub1, sub9115]
  rfl
theorem sub9131 (p : Pattern) : d3132 (change p 10000 none) = d3132 p := by
  change (if p 162 then d12 (change p 10000 none) else d3131 (change p 10000 none)) = d3132 p
  rw [sub1, sub9130]
  rfl
theorem sub9132 (p : Pattern) : d3133 (change p 10000 none) = d3133 p := by
  change (if p 161 then d12 (change p 10000 none) else d3132 (change p 10000 none)) = d3133 p
  rw [sub1, sub9131]
  rfl
theorem sub9133 (p : Pattern) : d3134 (change p 10000 none) = d3134 p := by
  change (if p 160 then d3133 (change p 10000 none) else d3130 (change p 10000 none)) = d3134 p
  rw [sub9132, sub9129]
  rfl
theorem sub9134 (p : Pattern) : d3135 (change p 10000 none) = d3135 p := by
  change (if p 141 then d3134 (change p 10000 none) else d3125 (change p 10000 none)) = d3135 p
  rw [sub9133, sub9119]
  rfl
theorem sub9135 (p : Pattern) : d3136 (change p 10000 none) = d3136 p := by
  change (if p 138 then d3135 (change p 10000 none) else d3113 (change p 10000 none)) = d3136 p
  rw [sub9134, sub9101]
  rfl
theorem sub9136 (p : Pattern) : d3137 (change p 10000 none) = d3137 p := by
  change (if p 138 then d12 (change p 10000 none) else d3135 (change p 10000 none)) = d3137 p
  rw [sub1, sub9134]
  rfl
theorem sub9137 (p : Pattern) : d3138 (change p 10000 none) = d3138 p := by
  change (if p 116 then d3137 (change p 10000 none) else d3136 (change p 10000 none)) = d3138 p
  rw [sub9136, sub9135]
  rfl
theorem sub9138 (p : Pattern) : d3139 (change p 10000 none) = d3139 p := by
  change (if p 115 then d3138 (change p 10000 none) else d2989 (change p 10000 none)) = d3139 p
  rw [sub9137, sub8912]
  rfl
theorem sub9139 (p : Pattern) : d3140 (change p 10000 none) = d3140 p := by
  change (if p 71 then d3139 (change p 10000 none) else d2992 (change p 10000 none)) = d3140 p
  rw [sub9138, sub8915]
  rfl
theorem sub9140 (p : Pattern) : d3141 (change p 10000 none) = d3141 p := by
  change (if p 163 then d12 (change p 10000 none) else d2996 (change p 10000 none)) = d3141 p
  rw [sub1, sub8937]
  rfl
theorem sub9141 (p : Pattern) : d3142 (change p 10000 none) = d3142 p := by
  change (if p 162 then d3141 (change p 10000 none) else d3017 (change p 10000 none)) = d3142 p
  rw [sub9140, sub8993]
  rfl
theorem sub9142 (p : Pattern) : d3143 (change p 10000 none) = d3143 p := by
  change (if p 162 then d12 (change p 10000 none) else d3141 (change p 10000 none)) = d3143 p
  rw [sub1, sub9140]
  rfl
theorem sub9143 (p : Pattern) : d3144 (change p 10000 none) = d3144 p := by
  change (if p 161 then d3143 (change p 10000 none) else d3142 (change p 10000 none)) = d3144 p
  rw [sub9142, sub9141]
  rfl
theorem sub9144 (p : Pattern) : d3145 (change p 10000 none) = d3145 p := by
  change (if p 163 then d12 (change p 10000 none) else d3008 (change p 10000 none)) = d3145 p
  rw [sub1, sub8977]
  rfl
theorem sub9145 (p : Pattern) : d3146 (change p 10000 none) = d3146 p := by
  change (if p 162 then d3145 (change p 10000 none) else d3025 (change p 10000 none)) = d3146 p
  rw [sub9144, sub9001]
  rfl
theorem sub9146 (p : Pattern) : d3147 (change p 10000 none) = d3147 p := by
  change (if p 162 then d12 (change p 10000 none) else d3145 (change p 10000 none)) = d3147 p
  rw [sub1, sub9144]
  rfl
theorem sub9147 (p : Pattern) : d3148 (change p 10000 none) = d3148 p := by
  change (if p 161 then d3147 (change p 10000 none) else d3146 (change p 10000 none)) = d3148 p
  rw [sub9146, sub9145]
  rfl
theorem sub9148 (p : Pattern) : d3149 (change p 10000 none) = d3149 p := by
  change (if p 160 then d3148 (change p 10000 none) else d3144 (change p 10000 none)) = d3149 p
  rw [sub9147, sub9143]
  rfl
theorem sub9149 (p : Pattern) : d3150 (change p 10000 none) = d3150 p := by
  change (if p 141 then d3149 (change p 10000 none) else d3014 (change p 10000 none)) = d3150 p
  rw [sub9148, sub8983]
  rfl
theorem sub9150 (p : Pattern) : d3151 (change p 10000 none) = d3151 p := by
  change (if p 163 then d12 (change p 10000 none) else d3043 (change p 10000 none)) = d3151 p
  rw [sub1, sub9029]
  rfl
theorem sub9151 (p : Pattern) : d3152 (change p 10000 none) = d3152 p := by
  change (if p 162 then d3151 (change p 10000 none) else d3055 (change p 10000 none)) = d3152 p
  rw [sub9150, sub9041]
  rfl
theorem sub9152 (p : Pattern) : d3153 (change p 10000 none) = d3153 p := by
  change (if p 162 then d12 (change p 10000 none) else d3151 (change p 10000 none)) = d3153 p
  rw [sub1, sub9150]
  rfl
theorem sub9153 (p : Pattern) : d3154 (change p 10000 none) = d3154 p := by
  change (if p 161 then d3153 (change p 10000 none) else d3152 (change p 10000 none)) = d3154 p
  rw [sub9152, sub9151]
  rfl
theorem sub9154 (p : Pattern) : d3155 (change p 10000 none) = d3155 p := by
  change (if p 160 then d3063 (change p 10000 none) else d3154 (change p 10000 none)) = d3155 p
  rw [sub9049, sub9153]
  rfl
theorem sub9155 (p : Pattern) : d3156 (change p 10000 none) = d3156 p := by
  change (if p 141 then d3155 (change p 10000 none) else d3054 (change p 10000 none)) = d3156 p
  rw [sub9154, sub9040]
  rfl
theorem sub9156 (p : Pattern) : d3157 (change p 10000 none) = d3157 p := by
  change (if p 138 then d3156 (change p 10000 none) else d3150 (change p 10000 none)) = d3157 p
  rw [sub9155, sub9149]
  rfl
theorem sub9157 (p : Pattern) : d3158 (change p 10000 none) = d3158 p := by
  change (if p 138 then d3070 (change p 10000 none) else d3156 (change p 10000 none)) = d3158 p
  rw [sub9056, sub9155]
  rfl
theorem sub9158 (p : Pattern) : d3159 (change p 10000 none) = d3159 p := by
  change (if p 116 then d3158 (change p 10000 none) else d3157 (change p 10000 none)) = d3159 p
  rw [sub9157, sub9156]
  rfl
theorem sub9159 (p : Pattern) : d3160 (change p 10000 none) = d3160 p := by
  change (if p 204 then d1951 (change p 10000 none) else d103 (change p 10000 none)) = d3160 p
  rw [sub9022, sub99]
  rfl
theorem sub9160 (p : Pattern) : d2109 (change p 10000 none) = d2109 p := by
  change (if p 204 then d12 (change p 10000 none) else d2108 (change p 10000 none)) = d2109 p
  rw [sub1, sub9010]
  rfl
theorem sub9161 (p : Pattern) : d3161 (change p 10000 none) = d3161 p := by
  change (if p 182 then d2109 (change p 10000 none) else d3160 (change p 10000 none)) = d3161 p
  rw [sub9160, sub9159]
  rfl
theorem sub9162 (p : Pattern) : d3162 (change p 10000 none) = d3162 p := by
  change (if p 163 then d3043 (change p 10000 none) else d3161 (change p 10000 none)) = d3162 p
  rw [sub9029, sub9161]
  rfl
theorem sub9163 (p : Pattern) : d3163 (change p 10000 none) = d3163 p := by
  change (if p 162 then d3162 (change p 10000 none) else d3034 (change p 10000 none)) = d3163 p
  rw [sub9162, sub9013]
  rfl
theorem sub9164 (p : Pattern) : d3164 (change p 10000 none) = d3164 p := by
  change (if p 163 then d3043 (change p 10000 none) else d3040 (change p 10000 none)) = d3164 p
  rw [sub9029, sub9024]
  rfl
theorem sub9165 (p : Pattern) : d3165 (change p 10000 none) = d3165 p := by
  change (if p 162 then d2999 (change p 10000 none) else d3164 (change p 10000 none)) = d3165 p
  rw [sub8940, sub9164]
  rfl
theorem sub9166 (p : Pattern) : d3166 (change p 10000 none) = d3166 p := by
  change (if p 161 then d3165 (change p 10000 none) else d3163 (change p 10000 none)) = d3166 p
  rw [sub9165, sub9163]
  rfl
theorem sub9167 (p : Pattern) : d3167 (change p 10000 none) = d3167 p := by
  change (if p 182 then d1906 (change p 10000 none) else d3023 (change p 10000 none)) = d3167 p
  rw [sub8966, sub8999]
  rfl
theorem sub9168 (p : Pattern) : d3168 (change p 10000 none) = d3168 p := by
  change (if p 163 then d3167 (change p 10000 none) else d3048 (change p 10000 none)) = d3168 p
  rw [sub9167, sub9034]
  rfl
theorem sub9169 (p : Pattern) : d3169 (change p 10000 none) = d3169 p := by
  change (if p 162 then d3145 (change p 10000 none) else d3168 (change p 10000 none)) = d3169 p
  rw [sub9144, sub9168]
  rfl
theorem sub9170 (p : Pattern) : d3170 (change p 10000 none) = d3170 p := by
  change (if p 182 then d12 (change p 10000 none) else d3049 (change p 10000 none)) = d3170 p
  rw [sub1, sub9035]
  rfl
theorem sub9171 (p : Pattern) : d3171 (change p 10000 none) = d3171 p := by
  change (if p 163 then d12 (change p 10000 none) else d3170 (change p 10000 none)) = d3171 p
  rw [sub1, sub9170]
  rfl
theorem sub9172 (p : Pattern) : d3172 (change p 10000 none) = d3172 p := by
  change (if p 162 then d12 (change p 10000 none) else d3171 (change p 10000 none)) = d3172 p
  rw [sub1, sub9171]
  rfl
theorem sub9173 (p : Pattern) : d3173 (change p 10000 none) = d3173 p := by
  change (if p 161 then d3172 (change p 10000 none) else d3169 (change p 10000 none)) = d3173 p
  rw [sub9172, sub9169]
  rfl
theorem sub9174 (p : Pattern) : d3174 (change p 10000 none) = d3174 p := by
  change (if p 160 then d3173 (change p 10000 none) else d3166 (change p 10000 none)) = d3174 p
  rw [sub9173, sub9166]
  rfl
theorem sub9175 (p : Pattern) : d3175 (change p 10000 none) = d3175 p := by
  change (if p 225 then d1892 (change p 10000 none) else d1895 (change p 10000 none)) = d3175 p
  rw [sub8951, sub8954]
  rfl
theorem sub9176 (p : Pattern) : d3176 (change p 10000 none) = d3176 p := by
  change (if p 224 then d3175 (change p 10000 none) else d1893 (change p 10000 none)) = d3176 p
  rw [sub9175, sub8952]
  rfl
theorem sub9177 (p : Pattern) : d3177 (change p 10000 none) = d3177 p := by
  change (if p 204 then d3176 (change p 10000 none) else d116 (change p 10000 none)) = d3177 p
  rw [sub9176, sub114]
  rfl
theorem sub9178 (p : Pattern) : d2126 (change p 10000 none) = d2126 p := by
  change (if p 204 then d12 (change p 10000 none) else d2125 (change p 10000 none)) = d2126 p
  rw [sub1, sub8985]
  rfl
theorem sub9179 (p : Pattern) : d3178 (change p 10000 none) = d3178 p := by
  change (if p 182 then d2126 (change p 10000 none) else d3177 (change p 10000 none)) = d3178 p
  rw [sub9178, sub9177]
  rfl
theorem sub9180 (p : Pattern) : d3179 (change p 10000 none) = d3179 p := by
  change (if p 163 then d3178 (change p 10000 none) else d3161 (change p 10000 none)) = d3179 p
  rw [sub9179, sub9161]
  rfl
theorem sub9181 (p : Pattern) : d2135 (change p 10000 none) = d2135 p := by
  change (if p 225 then d1961 (change p 10000 none) else d1964 (change p 10000 none)) = d2135 p
  rw [sub8971, sub8928]
  rfl
theorem sub9182 (p : Pattern) : d2136 (change p 10000 none) = d2136 p := by
  change (if p 224 then d2135 (change p 10000 none) else d1962 (change p 10000 none)) = d2136 p
  rw [sub9181, sub8972]
  rfl
theorem sub9183 (p : Pattern) : d3180 (change p 10000 none) = d3180 p := by
  change (if p 204 then d2136 (change p 10000 none) else d107 (change p 10000 none)) = d3180 p
  rw [sub9182, sub104]
  rfl
theorem sub9184 (p : Pattern) : d2131 (change p 10000 none) = d2131 p := by
  change (if p 204 then d12 (change p 10000 none) else d2130 (change p 10000 none)) = d2131 p
  rw [sub1, sub8930]
  rfl
theorem sub9185 (p : Pattern) : d3181 (change p 10000 none) = d3181 p := by
  change (if p 182 then d2131 (change p 10000 none) else d3180 (change p 10000 none)) = d3181 p
  rw [sub9184, sub9183]
  rfl
theorem sub9186 (p : Pattern) : d3182 (change p 10000 none) = d3182 p := by
  change (if p 163 then d12 (change p 10000 none) else d3181 (change p 10000 none)) = d3182 p
  rw [sub1, sub9185]
  rfl
theorem sub9187 (p : Pattern) : d3183 (change p 10000 none) = d3183 p := by
  change (if p 162 then d3182 (change p 10000 none) else d3179 (change p 10000 none)) = d3183 p
  rw [sub9186, sub9180]
  rfl
theorem sub9188 (p : Pattern) : d2137 (change p 10000 none) = d2137 p := by
  change (if p 204 then d12 (change p 10000 none) else d2136 (change p 10000 none)) = d2137 p
  rw [sub1, sub9182]
  rfl
theorem sub9189 (p : Pattern) : d3184 (change p 10000 none) = d3184 p := by
  change (if p 182 then d2137 (change p 10000 none) else d3007 (change p 10000 none)) = d3184 p
  rw [sub9188, sub8976]
  rfl
theorem sub9190 (p : Pattern) : d3185 (change p 10000 none) = d3185 p := by
  change (if p 163 then d12 (change p 10000 none) else d3184 (change p 10000 none)) = d3185 p
  rw [sub1, sub9189]
  rfl
theorem sub9191 (p : Pattern) : d3186 (change p 10000 none) = d3186 p := by
  change (if p 162 then d12 (change p 10000 none) else d3185 (change p 10000 none)) = d3186 p
  rw [sub1, sub9190]
  rfl
theorem sub9192 (p : Pattern) : d3187 (change p 10000 none) = d3187 p := by
  change (if p 161 then d3186 (change p 10000 none) else d3183 (change p 10000 none)) = d3187 p
  rw [sub9191, sub9187]
  rfl
theorem sub9193 (p : Pattern) : d3188 (change p 10000 none) = d3188 p := by
  change (if p 182 then d1906 (change p 10000 none) else d3007 (change p 10000 none)) = d3188 p
  rw [sub8966, sub8976]
  rfl
theorem sub9194 (p : Pattern) : d3189 (change p 10000 none) = d3189 p := by
  change (if p 163 then d3008 (change p 10000 none) else d3188 (change p 10000 none)) = d3189 p
  rw [sub8977, sub9193]
  rfl
theorem sub9195 (p : Pattern) : d3190 (change p 10000 none) = d3190 p := by
  change (if p 162 then d3171 (change p 10000 none) else d3189 (change p 10000 none)) = d3190 p
  rw [sub9171, sub9194]
  rfl
theorem sub9196 (p : Pattern) : d3191 (change p 10000 none) = d3191 p := by
  change (if p 162 then d12 (change p 10000 none) else d2918 (change p 10000 none)) = d3191 p
  rw [sub1, sub8816]
  rfl
theorem sub9197 (p : Pattern) : d3192 (change p 10000 none) = d3192 p := by
  change (if p 161 then d3191 (change p 10000 none) else d3190 (change p 10000 none)) = d3192 p
  rw [sub9196, sub9195]
  rfl
theorem sub9198 (p : Pattern) : d3193 (change p 10000 none) = d3193 p := by
  change (if p 160 then d3192 (change p 10000 none) else d3187 (change p 10000 none)) = d3193 p
  rw [sub9197, sub9192]
  rfl
theorem sub9199 (p : Pattern) : d3194 (change p 10000 none) = d3194 p := by
  change (if p 141 then d3193 (change p 10000 none) else d3174 (change p 10000 none)) = d3194 p
  rw [sub9198, sub9174]
  rfl
theorem sub9200 (p : Pattern) : d3195 (change p 10000 none) = d3195 p := by
  change (if p 163 then d3042 (change p 10000 none) else d3040 (change p 10000 none)) = d3195 p
  rw [sub9027, sub9024]
  rfl
theorem sub9201 (p : Pattern) : d3196 (change p 10000 none) = d3196 p := by
  change (if p 163 then d2931 (change p 10000 none) else d3048 (change p 10000 none)) = d3196 p
  rw [sub8839, sub9034]
  rfl
theorem sub9202 (p : Pattern) : d3197 (change p 10000 none) = d3197 p := by
  change (if p 162 then d3196 (change p 10000 none) else d3195 (change p 10000 none)) = d3197 p
  rw [sub9201, sub9200]
  rfl
theorem sub9203 (p : Pattern) : d3198 (change p 10000 none) = d3198 p := by
  change (if p 161 then d3059 (change p 10000 none) else d3197 (change p 10000 none)) = d3198 p
  rw [sub9045, sub9202]
  rfl
theorem sub9204 (p : Pattern) : d3199 (change p 10000 none) = d3199 p := by
  change (if p 160 then d3063 (change p 10000 none) else d3198 (change p 10000 none)) = d3199 p
  rw [sub9049, sub9203]
  rfl
theorem sub9205 (p : Pattern) : d2154 (change p 10000 none) = d2154 p := by
  change (if p 247 then d11 (change p 10000 none) else d3 (change p 10000 none)) = d2154 p
  rw [sub32, sub112]
  rfl
theorem sub9206 (p : Pattern) : d2155 (change p 10000 none) = d2155 p := by
  change (if p 246 then d39 (change p 10000 none) else d2154 (change p 10000 none)) = d2155 p
  rw [sub33, sub9205]
  rfl
theorem sub9207 (p : Pattern) : d2156 (change p 10000 none) = d2156 p := by
  change (if p 225 then d2155 (change p 10000 none) else d1895 (change p 10000 none)) = d2156 p
  rw [sub9206, sub8954]
  rfl
theorem sub9208 (p : Pattern) : d2157 (change p 10000 none) = d2157 p := by
  change (if p 224 then d2156 (change p 10000 none) else d1893 (change p 10000 none)) = d2157 p
  rw [sub9207, sub8952]
  rfl
theorem sub9209 (p : Pattern) : d2158 (change p 10000 none) = d2158 p := by
  change (if p 204 then d12 (change p 10000 none) else d2157 (change p 10000 none)) = d2158 p
  rw [sub1, sub9208]
  rfl
theorem sub9210 (p : Pattern) : d3200 (change p 10000 none) = d3200 p := by
  change (if p 182 then d2158 (change p 10000 none) else d3023 (change p 10000 none)) = d3200 p
  rw [sub9209, sub8999]
  rfl
theorem sub9211 (p : Pattern) : d3201 (change p 10000 none) = d3201 p := by
  change (if p 163 then d3048 (change p 10000 none) else d3200 (change p 10000 none)) = d3201 p
  rw [sub9034, sub9210]
  rfl
theorem sub9212 (p : Pattern) : d3202 (change p 10000 none) = d3202 p := by
  change (if p 162 then d3151 (change p 10000 none) else d3201 (change p 10000 none)) = d3202 p
  rw [sub9150, sub9211]
  rfl
theorem sub9213 (p : Pattern) : d3203 (change p 10000 none) = d3203 p := by
  change (if p 161 then d3062 (change p 10000 none) else d3202 (change p 10000 none)) = d3203 p
  rw [sub9048, sub9212]
  rfl
theorem sub9214 (p : Pattern) : d3204 (change p 10000 none) = d3204 p := by
  change (if p 162 then d12 (change p 10000 none) else d2958 (change p 10000 none)) = d3204 p
  rw [sub1, sub8881]
  rfl
theorem sub9215 (p : Pattern) : d3205 (change p 10000 none) = d3205 p := by
  change (if p 161 then d12 (change p 10000 none) else d3204 (change p 10000 none)) = d3205 p
  rw [sub1, sub9214]
  rfl
theorem sub9216 (p : Pattern) : d3206 (change p 10000 none) = d3206 p := by
  change (if p 160 then d3205 (change p 10000 none) else d3203 (change p 10000 none)) = d3206 p
  rw [sub9215, sub9213]
  rfl
theorem sub9217 (p : Pattern) : d3207 (change p 10000 none) = d3207 p := by
  change (if p 141 then d3206 (change p 10000 none) else d3199 (change p 10000 none)) = d3207 p
  rw [sub9216, sub9204]
  rfl
theorem sub9218 (p : Pattern) : d3208 (change p 10000 none) = d3208 p := by
  change (if p 138 then d3207 (change p 10000 none) else d3194 (change p 10000 none)) = d3208 p
  rw [sub9217, sub9199]
  rfl
theorem sub9219 (p : Pattern) : d3209 (change p 10000 none) = d3209 p := by
  change (if p 163 then d2957 (change p 10000 none) else d3048 (change p 10000 none)) = d3209 p
  rw [sub8880, sub9034]
  rfl
theorem sub9220 (p : Pattern) : d3210 (change p 10000 none) = d3210 p := by
  change (if p 162 then d3209 (change p 10000 none) else d3195 (change p 10000 none)) = d3210 p
  rw [sub9219, sub9200]
  rfl
theorem sub9221 (p : Pattern) : d3211 (change p 10000 none) = d3211 p := by
  change (if p 163 then d2957 (change p 10000 none) else d3043 (change p 10000 none)) = d3211 p
  rw [sub8880, sub9029]
  rfl
theorem sub9222 (p : Pattern) : d3212 (change p 10000 none) = d3212 p := by
  change (if p 162 then d12 (change p 10000 none) else d3211 (change p 10000 none)) = d3212 p
  rw [sub1, sub9221]
  rfl
theorem sub9223 (p : Pattern) : d3213 (change p 10000 none) = d3213 p := by
  change (if p 161 then d3212 (change p 10000 none) else d3210 (change p 10000 none)) = d3213 p
  rw [sub9222, sub9220]
  rfl
theorem sub9224 (p : Pattern) : d3214 (change p 10000 none) = d3214 p := by
  change (if p 163 then d2931 (change p 10000 none) else d3050 (change p 10000 none)) = d3214 p
  rw [sub8839, sub9036]
  rfl
theorem sub9225 (p : Pattern) : d3215 (change p 10000 none) = d3215 p := by
  change (if p 162 then d12 (change p 10000 none) else d3214 (change p 10000 none)) = d3215 p
  rw [sub1, sub9224]
  rfl
theorem sub9226 (p : Pattern) : d3216 (change p 10000 none) = d3216 p := by
  change (if p 161 then d12 (change p 10000 none) else d3215 (change p 10000 none)) = d3216 p
  rw [sub1, sub9225]
  rfl
theorem sub9227 (p : Pattern) : d3217 (change p 10000 none) = d3217 p := by
  change (if p 160 then d3216 (change p 10000 none) else d3213 (change p 10000 none)) = d3217 p
  rw [sub9226, sub9223]
  rfl
theorem sub9228 (p : Pattern) : d3218 (change p 10000 none) = d3218 p := by
  change (if p 141 then d3206 (change p 10000 none) else d3217 (change p 10000 none)) = d3218 p
  rw [sub9216, sub9227]
  rfl
theorem sub9229 (p : Pattern) : d3219 (change p 10000 none) = d3219 p := by
  change (if p 138 then d12 (change p 10000 none) else d3218 (change p 10000 none)) = d3219 p
  rw [sub1, sub9228]
  rfl
theorem sub9230 (p : Pattern) : d3220 (change p 10000 none) = d3220 p := by
  change (if p 116 then d3219 (change p 10000 none) else d3208 (change p 10000 none)) = d3220 p
  rw [sub9229, sub9218]
  rfl
theorem sub9231 (p : Pattern) : d3221 (change p 10000 none) = d3221 p := by
  change (if p 115 then d3220 (change p 10000 none) else d3159 (change p 10000 none)) = d3221 p
  rw [sub9230, sub9158]
  rfl
theorem sub9232 (p : Pattern) : d3222 (change p 10000 none) = d3222 p := by
  change (if p 71 then d3221 (change p 10000 none) else d2992 (change p 10000 none)) = d3222 p
  rw [sub9231, sub8915]
  rfl
theorem sub9233 (p : Pattern) : d3223 (change p 10000 none) = d3223 p := by
  change (if p 49 then d3222 (change p 10000 none) else d3140 (change p 10000 none)) = d3223 p
  rw [sub9232, sub9139]
  rfl
theorem sub9234 (p : Pattern) : d3224 (change p 10000 none) = d3224 p := by
  change (if p 48 then d3223 (change p 10000 none) else d3077 (change p 10000 none)) = d3224 p
  rw [sub9233, sub9063]
  rfl
theorem sub9235 (p : Pattern) : d0 (change p 224 (some 225)) = d0 p := by
  rfl
theorem sub9236 (p : Pattern) : d12 (change p 224 (some 225)) = d12 p := by
  rfl
theorem sub9237 (p : Pattern) : d13 (change p 224 (some 225)) = d13 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d0 (change p 224 (some 225))) = d13 p
  rw [sub9236, sub9235]
  rfl
theorem sub9238 (p : Pattern) : d14 (change p 224 (some 225)) = d14 p := by
  change (if p 246 then d13 (change p 224 (some 225)) else d0 (change p 224 (some 225))) = d14 p
  rw [sub9237, sub9235]
  rfl
theorem sub9239 (p : Pattern) : d2184 (change p 224 (some 225)) = d14 p := by
  change d14 (change p 224 (some 225)) = d14 p
  exact sub9238 p
end NetHack.Sokoban22Refined85
