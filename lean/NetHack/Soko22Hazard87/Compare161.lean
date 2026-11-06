import NetHack.Soko22Hazard87.Compare160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40250 (p : Pattern) (guard : d325000 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324998 p = 1 := by simpa only [d325000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40248 p hg
    simpa only [d325000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324999 p = 1 := by simpa only [d325000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40249 p hg
    simpa only [d325000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40251 (p : Pattern) (guard : d325001 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325000 p = 1 := by simpa only [d325001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40250 p hg
    simpa only [d325001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40252 (p : Pattern) (guard : d325002 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325001 p = 1 := by simpa only [d325002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40251 p hg
    simpa only [d325002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40253 (p : Pattern) (guard : d325003 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324962 p = 1 := by simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40212 p hg
    simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40254 (p : Pattern) (guard : d325004 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325003 p = 1 := by simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40253 p hg
    simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324924 p = 1 := by simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40173 p hg
    simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40255 (p : Pattern) (guard : d325005 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d325004 p = 1 := by simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40254 p hg
    simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40256 (p : Pattern) (guard : d325006 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324984 p = 1 := by simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40234 p hg
    simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40257 (p : Pattern) (guard : d325007 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325006 p = 1 := by simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40258 (p : Pattern) (guard : d325008 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d325007 p = 1 := by simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40257 p hg
    simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40259 (p : Pattern) (guard : d325009 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325005 p = 1 := by simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40255 p hg
    simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325008 p = 1 := by simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40258 p hg
    simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40260 (p : Pattern) (guard : d325010 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d325002 p = 1 := by simpa only [d325010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40252 p hg
    simpa only [d325010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325009 p = 1 := by simpa only [d325010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40259 p hg
    simpa only [d325010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40261 (p : Pattern) (guard : d325011 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d324997 p = 1 := by simpa only [d325011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40247 p hg
    simpa only [d325011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325010 p = 1 := by simpa only [d325011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40260 p hg
    simpa only [d325011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40262 (p : Pattern) (guard : d325012 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324990 p = 1 := by simpa only [d325012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40240 p hg
    simpa only [d325012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325011 p = 1 := by simpa only [d325012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40261 p hg
    simpa only [d325012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40263 (p : Pattern) (guard : d325013 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d324991 p = 1 := by simpa only [d325013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40241 p hg
    simpa only [d325013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325012 p = 1 := by simpa only [d325013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40262 p hg
    simpa only [d325013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40264 (p : Pattern) (guard : d325014 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324915 p = 1 := by simpa only [d325014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40164 p hg
    simpa only [d325014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40265 (p : Pattern) (guard : d325015 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325014 p = 1 := by simpa only [d325015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40264 p hg
    simpa only [d325015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40266 (p : Pattern) (guard : d325016 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325015 p = 1 := by simpa only [d325016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40265 p hg
    simpa only [d325016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40267 (p : Pattern) (guard : d325017 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325016 p = 1 := by simpa only [d325017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40266 p hg
    simpa only [d325017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40268 (p : Pattern) (guard : d325018 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325017 p = 1 := by simpa only [d325018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40267 p hg
    simpa only [d325018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40269 (p : Pattern) (guard : d325019 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324920 p = 1 := by simpa only [d325019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40169 p hg
    simpa only [d325019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325018 p = 1 := by simpa only [d325019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d325019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40270 (p : Pattern) (guard : d325020 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324925 p = 1 := by simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40174 p hg
    simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40271 (p : Pattern) (guard : d325021 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325020 p = 1 := by simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40270 p hg
    simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40272 (p : Pattern) (guard : d325022 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325021 p = 1 := by simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40271 p hg
    simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40273 (p : Pattern) (guard : d325023 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325022 p = 1 := by simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40272 p hg
    simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40274 (p : Pattern) (guard : d325024 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325023 p = 1 := by simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40273 p hg
    simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40275 (p : Pattern) (guard : d325025 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d325018 p = 1 := by simpa only [d325025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d325025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325024 p = 1 := by simpa only [d325025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40274 p hg
    simpa only [d325025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40276 (p : Pattern) (guard : d325026 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d325019 p = 1 := by simpa only [d325026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40269 p hg
    simpa only [d325026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325025 p = 1 := by simpa only [d325026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40275 p hg
    simpa only [d325026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40277 (p : Pattern) (guard : d325027 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d325013 p = 1 := by simpa only [d325027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40263 p hg
    simpa only [d325027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325026 p = 1 := by simpa only [d325027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40276 p hg
    simpa only [d325027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40278 (p : Pattern) (guard : d325028 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 51 with
  | false =>
    have hg : d325027 p = 1 := by simpa only [d325028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40277 p hg
    simpa only [d325028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40279 (p : Pattern) (guard : d325029 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 50 with
  | false =>
    have hg : d324934 p = 1 := by simpa only [d325029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40183 p hg
    simpa only [d325029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325028 p = 1 := by simpa only [d325029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40278 p hg
    simpa only [d325029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40280 (p : Pattern) (guard : d10055 p = 1) : d49565 p ≤ (1 : Int) + d49565 p := by
  omega
theorem compare40281 (p : Pattern) (guard : d38167 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40280 p hg
    simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40282 (p : Pattern) (guard : d38168 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40281 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40283 (p : Pattern) (guard : d38169 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40282 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40284 (p : Pattern) (guard : d38170 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40283 p hg
    simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39823 p hg
    simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40285 (p : Pattern) (guard : d38177 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39816 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40284 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40286 (p : Pattern) (guard : d38178 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40285 p hg
    simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40287 (p : Pattern) (guard : d38179 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38178 p = 1 := by simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40286 p hg
    simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40288 (p : Pattern) (guard : d38180 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38179 p = 1 := by simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40287 p hg
    simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40289 (p : Pattern) (guard : d38181 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d38180 p = 1 := by simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40288 p hg
    simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40290 (p : Pattern) (guard : d38302 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38181 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40289 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40291 (p : Pattern) (guard : d38303 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38302 p = 1 := by simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40290 p hg
    simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40292 (p : Pattern) (guard : d2043 p = 1) : d49565 p ≤ (1 : Int) + d49565 p := by
  omega
theorem compare40293 (p : Pattern) (guard : d221468 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40292 p hg
    simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40294 (p : Pattern) (guard : d221488 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40293 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40295 (p : Pattern) (guard : d10406 p = 1) : d49565 p ≤ (1 : Int) + d49565 p := by
  omega
theorem compare40296 (p : Pattern) (guard : d221489 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40295 p hg
    simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40297 (p : Pattern) (guard : d221490 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40296 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40298 (p : Pattern) (guard : d221491 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40294 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40297 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40299 (p : Pattern) (guard : d221492 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40298 p hg
    simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39823 p hg
    simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40300 (p : Pattern) (guard : d324882 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40284 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40299 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40301 (p : Pattern) (guard : d324883 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40300 p hg
    simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40302 (p : Pattern) (guard : d324884 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324883 p = 1 := by simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40301 p hg
    simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40303 (p : Pattern) (guard : d324885 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324884 p = 1 := by simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40302 p hg
    simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40304 (p : Pattern) (guard : d324886 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324885 p = 1 := by simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40303 p hg
    simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40305 (p : Pattern) (guard : d324887 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d38181 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40289 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324886 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40304 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40306 (p : Pattern) (guard : d324888 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d38302 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40290 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324887 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40305 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40307 (p : Pattern) (guard : d324952 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d38303 p = 1 := by simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40291 p hg
    simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324888 p = 1 := by simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40306 p hg
    simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40308 (p : Pattern) (guard : d324953 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324953, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324953, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324952 p = 1 := by simpa only [d324953, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40307 p hg
    simpa only [d324953, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40309 (p : Pattern) (guard : d324954 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324954, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324954, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324953 p = 1 := by simpa only [d324954, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40308 p hg
    simpa only [d324954, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40310 (p : Pattern) (guard : d324889 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324886 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40304 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40311 (p : Pattern) (guard : d324890 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324887 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40305 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324889 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40310 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40312 (p : Pattern) (guard : d324891 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324888 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40306 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324890 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40311 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40313 (p : Pattern) (guard : d324892 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324891 p = 1 := by simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40312 p hg
    simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40314 (p : Pattern) (guard : d324893 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324892 p = 1 := by simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40313 p hg
    simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40315 (p : Pattern) (guard : d324955 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324954 p = 1 := by simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40309 p hg
    simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324893 p = 1 := by simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40314 p hg
    simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40316 (p : Pattern) (guard : d221493 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40299 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39816 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40317 (p : Pattern) (guard : d221494 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40316 p hg
    simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40318 (p : Pattern) (guard : d221495 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221494 p = 1 := by simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40317 p hg
    simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40319 (p : Pattern) (guard : d221496 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221495 p = 1 := by simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40318 p hg
    simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40320 (p : Pattern) (guard : d221497 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221496 p = 1 := by simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40319 p hg
    simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40321 (p : Pattern) (guard : d221498 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221497 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40320 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40322 (p : Pattern) (guard : d324894 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324889 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40310 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221498 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40321 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40323 (p : Pattern) (guard : d324895 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324890 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40311 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324894 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40322 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40324 (p : Pattern) (guard : d324896 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324895 p = 1 := by simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40323 p hg
    simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40325 (p : Pattern) (guard : d324897 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324896 p = 1 := by simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40324 p hg
    simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40326 (p : Pattern) (guard : d324898 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324893 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40314 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324897 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40325 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40327 (p : Pattern) (guard : d324956 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324955 p = 1 := by simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40315 p hg
    simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324898 p = 1 := by simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40326 p hg
    simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40328 (p : Pattern) (guard : d324957 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324956 p = 1 := by simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40327 p hg
    simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40329 (p : Pattern) (guard : d324958 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324957 p = 1 := by simpa only [d324958, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40328 p hg
    simpa only [d324958, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324958, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324958, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40330 (p : Pattern) (guard : d324959 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324959, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324959, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324958 p = 1 := by simpa only [d324959, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40329 p hg
    simpa only [d324959, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40331 (p : Pattern) (guard : d324899 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324897 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40325 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40332 (p : Pattern) (guard : d324900 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324898 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40326 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324899 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40331 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40333 (p : Pattern) (guard : d324901 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324900 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40332 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40334 (p : Pattern) (guard : d324902 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324901 p = 1 := by simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40333 p hg
    simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40335 (p : Pattern) (guard : d324903 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324902 p = 1 := by simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40334 p hg
    simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40336 (p : Pattern) (guard : d324960 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324959 p = 1 := by simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40330 p hg
    simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324903 p = 1 := by simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40335 p hg
    simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40337 (p : Pattern) (guard : d324961 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324960 p = 1 := by simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40336 p hg
    simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40338 (p : Pattern) (guard : d324962 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324961 p = 1 := by simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40337 p hg
    simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40339 (p : Pattern) (guard : d325003 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324962 p = 1 := by simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40338 p hg
    simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40340 (p : Pattern) (guard : d324904 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324899 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40331 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40341 (p : Pattern) (guard : d324905 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324904 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40340 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40342 (p : Pattern) (guard : d324906 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324905 p = 1 := by simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40341 p hg
    simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40343 (p : Pattern) (guard : d324907 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324906 p = 1 := by simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40342 p hg
    simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40344 (p : Pattern) (guard : d324908 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324903 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40335 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324907 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40343 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40345 (p : Pattern) (guard : d324909 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324908 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40344 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40346 (p : Pattern) (guard : d324910 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324909 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40345 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40347 (p : Pattern) (guard : d324924 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324910 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40346 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40348 (p : Pattern) (guard : d325004 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325003 p = 1 := by simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40339 p hg
    simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324924 p = 1 := by simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40347 p hg
    simpa only [d325004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40349 (p : Pattern) (guard : d325005 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d325004 p = 1 := by simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40348 p hg
    simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40350 (p : Pattern) (guard : d324966 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40284 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39816 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40351 (p : Pattern) (guard : d324967 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324966 p = 1 := by simpa only [d324967, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40350 p hg
    simpa only [d324967, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324967, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324967, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40352 (p : Pattern) (guard : d324968 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324967 p = 1 := by simpa only [d324968, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40351 p hg
    simpa only [d324968, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324968, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324968, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40353 (p : Pattern) (guard : d324969 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324969, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d324969, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324968 p = 1 := by simpa only [d324969, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40352 p hg
    simpa only [d324969, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40354 (p : Pattern) (guard : d324970 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324969 p = 1 := by simpa only [d324970, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40353 p hg
    simpa only [d324970, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324970, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d324970, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40355 (p : Pattern) (guard : d324971 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324970 p = 1 := by simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40354 p hg
    simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40356 (p : Pattern) (guard : d324972 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324887 p = 1 := by simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40305 p hg
    simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324971 p = 1 := by simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40355 p hg
    simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40357 (p : Pattern) (guard : d324973 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324971 p = 1 := by simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40355 p hg
    simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40358 (p : Pattern) (guard : d324974 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324972 p = 1 := by simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40356 p hg
    simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324973 p = 1 := by simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40357 p hg
    simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40359 (p : Pattern) (guard : d324975 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324975, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324975, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324974 p = 1 := by simpa only [d324975, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40358 p hg
    simpa only [d324975, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40360 (p : Pattern) (guard : d324976 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324976, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324976, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324975 p = 1 := by simpa only [d324976, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40359 p hg
    simpa only [d324976, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40361 (p : Pattern) (guard : d324977 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324976 p = 1 := by simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40360 p hg
    simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40362 (p : Pattern) (guard : d324978 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324898 p = 1 := by simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40326 p hg
    simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324977 p = 1 := by simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40361 p hg
    simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40363 (p : Pattern) (guard : d324979 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324978 p = 1 := by simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40362 p hg
    simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40364 (p : Pattern) (guard : d324980 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324979 p = 1 := by simpa only [d324980, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40363 p hg
    simpa only [d324980, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324980, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324980, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40365 (p : Pattern) (guard : d324981 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324981, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324981, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324980 p = 1 := by simpa only [d324981, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40364 p hg
    simpa only [d324981, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40366 (p : Pattern) (guard : d324982 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324981 p = 1 := by simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40365 p hg
    simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40367 (p : Pattern) (guard : d324983 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324982 p = 1 := by simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40366 p hg
    simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40368 (p : Pattern) (guard : d324984 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324983 p = 1 := by simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40367 p hg
    simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40369 (p : Pattern) (guard : d325006 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324984 p = 1 := by simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40368 p hg
    simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40370 (p : Pattern) (guard : d325007 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325006 p = 1 := by simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40369 p hg
    simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40371 (p : Pattern) (guard : d325008 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d325007 p = 1 := by simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40370 p hg
    simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40372 (p : Pattern) (guard : d325009 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325005 p = 1 := by simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40349 p hg
    simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325008 p = 1 := by simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40371 p hg
    simpa only [d325009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40373 (p : Pattern) (guard : d325030 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325009 p = 1 := by simpa only [d325030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40372 p hg
    simpa only [d325030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40374 (p : Pattern) (guard : d325031 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325030 p = 1 := by simpa only [d325031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40373 p hg
    simpa only [d325031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40375 (p : Pattern) (guard : d325032 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325032, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325032, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325031 p = 1 := by simpa only [d325032, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40374 p hg
    simpa only [d325032, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40376 (p : Pattern) (guard : d325033 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d325033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325032 p = 1 := by simpa only [d325033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40375 p hg
    simpa only [d325033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40377 (p : Pattern) (guard : d324912 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324907 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40343 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40378 (p : Pattern) (guard : d324913 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324912 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40377 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40379 (p : Pattern) (guard : d324914 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324913 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40378 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40380 (p : Pattern) (guard : d324925 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324914 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40379 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40381 (p : Pattern) (guard : d325020 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324925 p = 1 := by simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40380 p hg
    simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40382 (p : Pattern) (guard : d325021 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325020 p = 1 := by simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40381 p hg
    simpa only [d325021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40383 (p : Pattern) (guard : d325022 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325021 p = 1 := by simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40382 p hg
    simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40384 (p : Pattern) (guard : d325023 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325022 p = 1 := by simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40383 p hg
    simpa only [d325023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40385 (p : Pattern) (guard : d325024 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325023 p = 1 := by simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40384 p hg
    simpa only [d325024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40386 (p : Pattern) (guard : d325034 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325034, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d325034, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325024 p = 1 := by simpa only [d325034, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40385 p hg
    simpa only [d325034, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40387 (p : Pattern) (guard : d325035 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d325035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325034 p = 1 := by simpa only [d325035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40386 p hg
    simpa only [d325035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40388 (p : Pattern) (guard : d325036 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 69 with
  | false =>
    have hg : d325033 p = 1 := by simpa only [d325036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40376 p hg
    simpa only [d325036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325035 p = 1 := by simpa only [d325036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40387 p hg
    simpa only [d325036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40389 (p : Pattern) (guard : d325037 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 51 with
  | false =>
    have hg : d325036 p = 1 := by simpa only [d325037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40388 p hg
    simpa only [d325037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d325037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40390 (p : Pattern) (guard : d325038 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 50 with
  | false =>
    have hg : d325037 p = 1 := by simpa only [d325038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40389 p hg
    simpa only [d325038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d325038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40391 (p : Pattern) (guard : d325039 p = 1) : d50676 p ≤ (1 : Int) + d324519 p := by
  cases selected : p 49 with
  | false =>
    have hg : d325029 p = 1 := by simpa only [d325039, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40279 p hg
    simpa only [d325039, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325038 p = 1 := by simpa only [d325039, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40390 p hg
    simpa only [d325039, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40392 (p : Pattern) (guard : d10055 p = 1) : d49316 p ≤ (1 : Int) + d49316 p := by
  omega
theorem compare40393 (p : Pattern) (guard : d38167 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40392 p hg
    simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40394 (p : Pattern) (guard : d38168 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40393 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40395 (p : Pattern) (guard : d38169 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40394 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40396 (p : Pattern) (guard : d38170 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40395 p hg
    simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39949 p hg
    simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40397 (p : Pattern) (guard : d38177 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39942 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40396 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40398 (p : Pattern) (guard : d38532 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38177 p = 1 := by simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40397 p hg
    simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40399 (p : Pattern) (guard : d38178 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40111 p hg
    simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40400 (p : Pattern) (guard : d38533 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38532 p = 1 := by simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40398 p hg
    simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38178 p = 1 := by simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40399 p hg
    simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40401 (p : Pattern) (guard : d10055 p = 1) : d49323 p ≤ (1 : Int) + d49323 p := by
  omega
theorem compare40402 (p : Pattern) (guard : d38167 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40401 p hg
    simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40403 (p : Pattern) (guard : d38168 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40402 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40404 (p : Pattern) (guard : d38169 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40403 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40405 (p : Pattern) (guard : d38170 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40404 p hg
    simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39962 p hg
    simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40406 (p : Pattern) (guard : d38177 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39955 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40405 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40407 (p : Pattern) (guard : d38178 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40406 p hg
    simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40408 (p : Pattern) (guard : d38179 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38178 p = 1 := by simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40407 p hg
    simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40409 (p : Pattern) (guard : d38534 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d38533 p = 1 := by simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40400 p hg
    simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38179 p = 1 := by simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40408 p hg
    simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40410 (p : Pattern) (guard : d38535 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d38534 p = 1 := by simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40409 p hg
    simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40411 (p : Pattern) (guard : d38536 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38535 p = 1 := by simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40410 p hg
    simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40412 (p : Pattern) (guard : d38537 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d38537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38536 p = 1 := by simpa only [d38537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40411 p hg
    simpa only [d38537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40413 (p : Pattern) (guard : d2043 p = 1) : d49316 p ≤ (1 : Int) + d49316 p := by
  omega
theorem compare40414 (p : Pattern) (guard : d221468 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40413 p hg
    simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40415 (p : Pattern) (guard : d221488 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40414 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40416 (p : Pattern) (guard : d10406 p = 1) : d49316 p ≤ (1 : Int) + d49316 p := by
  omega
theorem compare40417 (p : Pattern) (guard : d221489 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40416 p hg
    simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40418 (p : Pattern) (guard : d221490 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40417 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40419 (p : Pattern) (guard : d221491 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40415 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40418 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40420 (p : Pattern) (guard : d221492 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39949 p hg
    simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40421 (p : Pattern) (guard : d324882 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40396 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40420 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40422 (p : Pattern) (guard : d325040 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324882 p = 1 := by simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40421 p hg
    simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40423 (p : Pattern) (guard : d324883 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40125 p hg
    simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40424 (p : Pattern) (guard : d325041 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d325040 p = 1 := by simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40422 p hg
    simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324883 p = 1 := by simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40423 p hg
    simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40425 (p : Pattern) (guard : d2043 p = 1) : d49323 p ≤ (1 : Int) + d49323 p := by
  omega
theorem compare40426 (p : Pattern) (guard : d221468 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40425 p hg
    simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40427 (p : Pattern) (guard : d221488 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40426 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40428 (p : Pattern) (guard : d10406 p = 1) : d49323 p ≤ (1 : Int) + d49323 p := by
  omega
theorem compare40429 (p : Pattern) (guard : d221489 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40428 p hg
    simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40430 (p : Pattern) (guard : d221490 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40429 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40431 (p : Pattern) (guard : d221491 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40427 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40430 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40432 (p : Pattern) (guard : d221492 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40431 p hg
    simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39962 p hg
    simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40433 (p : Pattern) (guard : d324882 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40405 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40432 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40434 (p : Pattern) (guard : d324883 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40433 p hg
    simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40435 (p : Pattern) (guard : d324884 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324883 p = 1 := by simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40434 p hg
    simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40436 (p : Pattern) (guard : d325042 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d325041 p = 1 := by simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40424 p hg
    simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324884 p = 1 := by simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40435 p hg
    simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40437 (p : Pattern) (guard : d325043 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d325042 p = 1 := by simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40436 p hg
    simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40438 (p : Pattern) (guard : d325044 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d38535 p = 1 := by simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40410 p hg
    simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325043 p = 1 := by simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40437 p hg
    simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40439 (p : Pattern) (guard : d325045 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d38536 p = 1 := by simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40411 p hg
    simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325044 p = 1 := by simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40438 p hg
    simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40440 (p : Pattern) (guard : d325046 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d38537 p = 1 := by simpa only [d325046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d325046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325045 p = 1 := by simpa only [d325046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40439 p hg
    simpa only [d325046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40441 (p : Pattern) (guard : d325047 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325047, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d325047, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325046 p = 1 := by simpa only [d325047, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40440 p hg
    simpa only [d325047, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40442 (p : Pattern) (guard : d325048 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325048, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d325048, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325047 p = 1 := by simpa only [d325048, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40441 p hg
    simpa only [d325048, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40443 (p : Pattern) (guard : d325049 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d325043 p = 1 := by simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40437 p hg
    simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40444 (p : Pattern) (guard : d325050 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d325044 p = 1 := by simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40438 p hg
    simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325049 p = 1 := by simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40443 p hg
    simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40445 (p : Pattern) (guard : d325051 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d325045 p = 1 := by simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40439 p hg
    simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325050 p = 1 := by simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40444 p hg
    simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40446 (p : Pattern) (guard : d325052 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325051 p = 1 := by simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40445 p hg
    simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40447 (p : Pattern) (guard : d325053 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325052 p = 1 := by simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40446 p hg
    simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40448 (p : Pattern) (guard : d325054 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d325048 p = 1 := by simpa only [d325054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40442 p hg
    simpa only [d325054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325053 p = 1 := by simpa only [d325054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40447 p hg
    simpa only [d325054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40449 (p : Pattern) (guard : d221493 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40420 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39942 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40450 (p : Pattern) (guard : d221734 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221493 p = 1 := by simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40449 p hg
    simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40451 (p : Pattern) (guard : d221494 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40137 p hg
    simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40452 (p : Pattern) (guard : d221735 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221734 p = 1 := by simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40450 p hg
    simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221494 p = 1 := by simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40451 p hg
    simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40453 (p : Pattern) (guard : d221493 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40432 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39955 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40454 (p : Pattern) (guard : d221494 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40453 p hg
    simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40455 (p : Pattern) (guard : d221495 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221494 p = 1 := by simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40454 p hg
    simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40456 (p : Pattern) (guard : d221736 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d221735 p = 1 := by simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40452 p hg
    simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221495 p = 1 := by simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40455 p hg
    simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40457 (p : Pattern) (guard : d221737 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221736 p = 1 := by simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40456 p hg
    simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40458 (p : Pattern) (guard : d221738 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221737 p = 1 := by simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40459 (p : Pattern) (guard : d325055 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d325049 p = 1 := by simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40443 p hg
    simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221738 p = 1 := by simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40458 p hg
    simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40460 (p : Pattern) (guard : d325056 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d325050 p = 1 := by simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40444 p hg
    simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325055 p = 1 := by simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40459 p hg
    simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40461 (p : Pattern) (guard : d325057 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325056 p = 1 := by simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40460 p hg
    simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40462 (p : Pattern) (guard : d325058 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325057 p = 1 := by simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40463 (p : Pattern) (guard : d325059 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d325053 p = 1 := by simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40447 p hg
    simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325058 p = 1 := by simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40462 p hg
    simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40464 (p : Pattern) (guard : d325060 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d325054 p = 1 := by simpa only [d325060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40448 p hg
    simpa only [d325060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325059 p = 1 := by simpa only [d325060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40463 p hg
    simpa only [d325060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40465 (p : Pattern) (guard : d325061 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d325060 p = 1 := by simpa only [d325061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40464 p hg
    simpa only [d325061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d325061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40466 (p : Pattern) (guard : d325062 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d325061 p = 1 := by simpa only [d325062, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40465 p hg
    simpa only [d325062, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325062, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d325062, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40467 (p : Pattern) (guard : d325063 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325063, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d325063, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325062 p = 1 := by simpa only [d325063, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40466 p hg
    simpa only [d325063, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40468 (p : Pattern) (guard : d325064 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d325058 p = 1 := by simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40462 p hg
    simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40469 (p : Pattern) (guard : d325065 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d325059 p = 1 := by simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40463 p hg
    simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325064 p = 1 := by simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40468 p hg
    simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40470 (p : Pattern) (guard : d325066 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d325065 p = 1 := by simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40469 p hg
    simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40471 (p : Pattern) (guard : d325067 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d325066 p = 1 := by simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40470 p hg
    simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40472 (p : Pattern) (guard : d325068 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325067 p = 1 := by simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40471 p hg
    simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40473 (p : Pattern) (guard : d325069 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d325063 p = 1 := by simpa only [d325069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40467 p hg
    simpa only [d325069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325068 p = 1 := by simpa only [d325069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40472 p hg
    simpa only [d325069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40474 (p : Pattern) (guard : d325070 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d325069 p = 1 := by simpa only [d325070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40473 p hg
    simpa only [d325070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40475 (p : Pattern) (guard : d325071 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d325070 p = 1 := by simpa only [d325071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40474 p hg
    simpa only [d325071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40476 (p : Pattern) (guard : d325072 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d325071 p = 1 := by simpa only [d325072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40475 p hg
    simpa only [d325072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40477 (p : Pattern) (guard : d325073 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d325064 p = 1 := by simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40468 p hg
    simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40478 (p : Pattern) (guard : d325074 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d325073 p = 1 := by simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40477 p hg
    simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40479 (p : Pattern) (guard : d325075 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d325074 p = 1 := by simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40478 p hg
    simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40480 (p : Pattern) (guard : d325076 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325075 p = 1 := by simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40479 p hg
    simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40481 (p : Pattern) (guard : d325077 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d325068 p = 1 := by simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40472 p hg
    simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325076 p = 1 := by simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40480 p hg
    simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40482 (p : Pattern) (guard : d325078 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d325077 p = 1 := by simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40481 p hg
    simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40483 (p : Pattern) (guard : d325079 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d325078 p = 1 := by simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40482 p hg
    simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40484 (p : Pattern) (guard : d325080 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d325079 p = 1 := by simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40483 p hg
    simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40485 (p : Pattern) (guard : d325081 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325072 p = 1 := by simpa only [d325081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40476 p hg
    simpa only [d325081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325080 p = 1 := by simpa only [d325081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40484 p hg
    simpa only [d325081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40486 (p : Pattern) (guard : d325082 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d325081 p = 1 := by simpa only [d325082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40485 p hg
    simpa only [d325082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d325082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40487 (p : Pattern) (guard : d324966 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40396 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39942 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40488 (p : Pattern) (guard : d325083 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325083, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d325083, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324966 p = 1 := by simpa only [d325083, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40487 p hg
    simpa only [d325083, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40489 (p : Pattern) (guard : d324967 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324966 p = 1 := by simpa only [d324967, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40216 p hg
    simpa only [d324967, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324967, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324967, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40490 (p : Pattern) (guard : d325084 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d325083 p = 1 := by simpa only [d325084, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40488 p hg
    simpa only [d325084, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324967 p = 1 := by simpa only [d325084, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40489 p hg
    simpa only [d325084, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40491 (p : Pattern) (guard : d324966 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40405 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39955 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40492 (p : Pattern) (guard : d324967 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324966 p = 1 := by simpa only [d324967, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40491 p hg
    simpa only [d324967, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324967, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324967, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40493 (p : Pattern) (guard : d324968 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324967 p = 1 := by simpa only [d324968, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40492 p hg
    simpa only [d324968, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324968, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324968, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40494 (p : Pattern) (guard : d325085 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d325084 p = 1 := by simpa only [d325085, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40490 p hg
    simpa only [d325085, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324968 p = 1 := by simpa only [d325085, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40493 p hg
    simpa only [d325085, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40495 (p : Pattern) (guard : d325086 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d325085 p = 1 := by simpa only [d325086, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40494 p hg
    simpa only [d325086, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325086, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d325086, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40496 (p : Pattern) (guard : d325087 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d325086 p = 1 := by simpa only [d325087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40495 p hg
    simpa only [d325087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d325087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40497 (p : Pattern) (guard : d325088 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d325044 p = 1 := by simpa only [d325088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40438 p hg
    simpa only [d325088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325087 p = 1 := by simpa only [d325088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40496 p hg
    simpa only [d325088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40498 (p : Pattern) (guard : d325089 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d325087 p = 1 := by simpa only [d325089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40496 p hg
    simpa only [d325089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d325089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40499 (p : Pattern) (guard : d325090 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d325088 p = 1 := by simpa only [d325090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40497 p hg
    simpa only [d325090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325089 p = 1 := by simpa only [d325090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40498 p hg
    simpa only [d325090, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
