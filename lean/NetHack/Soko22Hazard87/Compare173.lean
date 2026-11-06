import NetHack.Soko22Hazard87.Compare172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43250 (p : Pattern) (guard : d342931 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342930 p = 1 := by simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43249 p hg
    simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43251 (p : Pattern) (guard : d342932 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342931 p = 1 := by simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43250 p hg
    simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342806 p = 1 := by simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43074 p hg
    simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43252 (p : Pattern) (guard : d342933 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342932 p = 1 := by simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43251 p hg
    simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43253 (p : Pattern) (guard : d342934 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342933 p = 1 := by simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43252 p hg
    simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43254 (p : Pattern) (guard : d342935 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342934 p = 1 := by simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43253 p hg
    simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43255 (p : Pattern) (guard : d342936 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342839 p = 1 := by simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43098 p hg
    simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43256 (p : Pattern) (guard : d342937 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342936 p = 1 := by simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43255 p hg
    simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43257 (p : Pattern) (guard : d342938 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342937 p = 1 := by simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43256 p hg
    simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43258 (p : Pattern) (guard : d342939 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342938 p = 1 := by simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43257 p hg
    simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342813 p = 1 := by simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43081 p hg
    simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43259 (p : Pattern) (guard : d342940 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342939 p = 1 := by simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43258 p hg
    simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43260 (p : Pattern) (guard : d342941 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342940 p = 1 := by simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43259 p hg
    simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43261 (p : Pattern) (guard : d366229 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43262 (p : Pattern) (guard : d366230 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366229 p = 1 := by simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43261 p hg
    simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43263 (p : Pattern) (guard : d366231 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366230 p = 1 := by simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43262 p hg
    simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43264 (p : Pattern) (guard : d366232 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366231 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43263 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342828 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43087 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43265 (p : Pattern) (guard : d342963 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43266 (p : Pattern) (guard : d342964 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342963 p = 1 := by simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43265 p hg
    simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43267 (p : Pattern) (guard : d342965 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342964 p = 1 := by simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43266 p hg
    simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43268 (p : Pattern) (guard : d342966 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342965 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43267 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42905 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43269 (p : Pattern) (guard : d366233 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366232 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43264 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342966 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43268 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43270 (p : Pattern) (guard : d366234 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366233 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43269 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342830 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43089 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43271 (p : Pattern) (guard : d366235 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366234 p = 1 := by simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43270 p hg
    simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43272 (p : Pattern) (guard : d366236 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366235 p = 1 := by simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43271 p hg
    simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43273 (p : Pattern) (guard : d366237 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366236 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43272 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342833 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43092 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43274 (p : Pattern) (guard : d366238 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366237 p = 1 := by simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43273 p hg
    simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342834 p = 1 := by simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43093 p hg
    simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43275 (p : Pattern) (guard : d366239 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366238 p = 1 := by simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43274 p hg
    simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43276 (p : Pattern) (guard : d366240 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366239 p = 1 := by simpa only [d366240, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43275 p hg
    simpa only [d366240, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366240, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366240, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43277 (p : Pattern) (guard : d366241 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366241, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366241, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366240 p = 1 := by simpa only [d366241, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43276 p hg
    simpa only [d366241, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43278 (p : Pattern) (guard : d366242 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366241 p = 1 := by simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43277 p hg
    simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342838 p = 1 := by simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43097 p hg
    simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43279 (p : Pattern) (guard : d366243 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366242 p = 1 := by simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43278 p hg
    simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43280 (p : Pattern) (guard : d366244 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366243 p = 1 := by simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43279 p hg
    simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43281 (p : Pattern) (guard : d366245 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366244 p = 1 := by simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43280 p hg
    simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43282 (p : Pattern) (guard : d366246 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366245 p = 1 := by simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43281 p hg
    simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342842 p = 1 := by simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43101 p hg
    simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43283 (p : Pattern) (guard : d366247 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366246 p = 1 := by simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43282 p hg
    simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43284 (p : Pattern) (guard : d342982 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43097 p hg
    simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43285 (p : Pattern) (guard : d342983 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342982 p = 1 := by simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43284 p hg
    simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43286 (p : Pattern) (guard : d342984 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342983 p = 1 := by simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43285 p hg
    simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43287 (p : Pattern) (guard : d342985 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342984 p = 1 := by simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43286 p hg
    simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43288 (p : Pattern) (guard : d342986 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342985 p = 1 := by simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43287 p hg
    simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43289 (p : Pattern) (guard : d342987 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342986 p = 1 := by simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43288 p hg
    simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43290 (p : Pattern) (guard : d366248 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366247 p = 1 := by simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43283 p hg
    simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342987 p = 1 := by simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43289 p hg
    simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43291 (p : Pattern) (guard : d366249 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d342941 p = 1 := by simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43260 p hg
    simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366248 p = 1 := by simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43290 p hg
    simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43292 (p : Pattern) (guard : d366250 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d342935 p = 1 := by simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43254 p hg
    simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366249 p = 1 := by simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43291 p hg
    simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43293 (p : Pattern) (guard : d366251 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366251, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366251, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366250 p = 1 := by simpa only [d366251, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43292 p hg
    simpa only [d366251, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43294 (p : Pattern) (guard : d342930 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342840 p = 1 := by simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43122 p hg
    simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43295 (p : Pattern) (guard : d342931 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342930 p = 1 := by simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43294 p hg
    simpa only [d342931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43296 (p : Pattern) (guard : d342932 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342931 p = 1 := by simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43295 p hg
    simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342806 p = 1 := by simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43109 p hg
    simpa only [d342932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43297 (p : Pattern) (guard : d342933 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342932 p = 1 := by simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43296 p hg
    simpa only [d342933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43298 (p : Pattern) (guard : d342934 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342933 p = 1 := by simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43297 p hg
    simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43299 (p : Pattern) (guard : d342935 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342934 p = 1 := by simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43298 p hg
    simpa only [d342935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43300 (p : Pattern) (guard : d342936 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342839 p = 1 := by simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43121 p hg
    simpa only [d342936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43301 (p : Pattern) (guard : d342937 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342936 p = 1 := by simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43300 p hg
    simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43302 (p : Pattern) (guard : d342938 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342937 p = 1 := by simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43301 p hg
    simpa only [d342938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43303 (p : Pattern) (guard : d342939 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342938 p = 1 := by simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43302 p hg
    simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342813 p = 1 := by simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43116 p hg
    simpa only [d342939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43304 (p : Pattern) (guard : d342940 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342939 p = 1 := by simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43303 p hg
    simpa only [d342940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43305 (p : Pattern) (guard : d342941 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342940 p = 1 := by simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43304 p hg
    simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43306 (p : Pattern) (guard : d366241 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366241, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366241, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366240 p = 1 := by simpa only [d366241, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43276 p hg
    simpa only [d366241, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43307 (p : Pattern) (guard : d366242 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366241 p = 1 := by simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43306 p hg
    simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342838 p = 1 := by simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43120 p hg
    simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43308 (p : Pattern) (guard : d366243 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366242 p = 1 := by simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43307 p hg
    simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43309 (p : Pattern) (guard : d366244 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366243 p = 1 := by simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43308 p hg
    simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43310 (p : Pattern) (guard : d366245 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366244 p = 1 := by simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43309 p hg
    simpa only [d366245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43311 (p : Pattern) (guard : d366246 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366245 p = 1 := by simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43310 p hg
    simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342842 p = 1 := by simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43124 p hg
    simpa only [d366246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43312 (p : Pattern) (guard : d366247 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366246 p = 1 := by simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43311 p hg
    simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43313 (p : Pattern) (guard : d342982 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43120 p hg
    simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43314 (p : Pattern) (guard : d342983 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342982 p = 1 := by simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43313 p hg
    simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43315 (p : Pattern) (guard : d342984 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342983 p = 1 := by simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43314 p hg
    simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43316 (p : Pattern) (guard : d342985 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342984 p = 1 := by simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43315 p hg
    simpa only [d342985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43317 (p : Pattern) (guard : d342986 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342985 p = 1 := by simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43316 p hg
    simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43318 (p : Pattern) (guard : d342987 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342986 p = 1 := by simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43317 p hg
    simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43319 (p : Pattern) (guard : d366248 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366247 p = 1 := by simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43312 p hg
    simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342987 p = 1 := by simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43318 p hg
    simpa only [d366248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43320 (p : Pattern) (guard : d366249 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d342941 p = 1 := by simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43305 p hg
    simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366248 p = 1 := by simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43319 p hg
    simpa only [d366249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43321 (p : Pattern) (guard : d366250 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d342935 p = 1 := by simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43299 p hg
    simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366249 p = 1 := by simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43320 p hg
    simpa only [d366250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43322 (p : Pattern) (guard : d342992 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342930 p = 1 := by simpa only [d342992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43249 p hg
    simpa only [d342992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43323 (p : Pattern) (guard : d342993 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342992 p = 1 := by simpa only [d342993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43322 p hg
    simpa only [d342993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342849 p = 1 := by simpa only [d342993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43130 p hg
    simpa only [d342993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43324 (p : Pattern) (guard : d342994 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342993 p = 1 := by simpa only [d342994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43323 p hg
    simpa only [d342994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43325 (p : Pattern) (guard : d342995 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342994 p = 1 := by simpa only [d342995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43324 p hg
    simpa only [d342995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43326 (p : Pattern) (guard : d342996 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342995 p = 1 := by simpa only [d342996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43325 p hg
    simpa only [d342996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43327 (p : Pattern) (guard : d342997 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342937 p = 1 := by simpa only [d342997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43256 p hg
    simpa only [d342997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43328 (p : Pattern) (guard : d342998 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342997 p = 1 := by simpa only [d342998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43327 p hg
    simpa only [d342998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342854 p = 1 := by simpa only [d342998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43135 p hg
    simpa only [d342998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43329 (p : Pattern) (guard : d342999 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342998 p = 1 := by simpa only [d342999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43328 p hg
    simpa only [d342999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43330 (p : Pattern) (guard : d343000 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342999 p = 1 := by simpa only [d343000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43329 p hg
    simpa only [d343000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43331 (p : Pattern) (guard : d366252 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366244 p = 1 := by simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43280 p hg
    simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43332 (p : Pattern) (guard : d366253 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366252 p = 1 := by simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43331 p hg
    simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342858 p = 1 := by simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43139 p hg
    simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43333 (p : Pattern) (guard : d366254 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366253 p = 1 := by simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43332 p hg
    simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43334 (p : Pattern) (guard : d343004 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342984 p = 1 := by simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43286 p hg
    simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43335 (p : Pattern) (guard : d343005 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343004 p = 1 := by simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43334 p hg
    simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43336 (p : Pattern) (guard : d343006 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d343005 p = 1 := by simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43335 p hg
    simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43337 (p : Pattern) (guard : d366255 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366254 p = 1 := by simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43333 p hg
    simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343006 p = 1 := by simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43336 p hg
    simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43338 (p : Pattern) (guard : d366256 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d343000 p = 1 := by simpa only [d366256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43330 p hg
    simpa only [d366256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366255 p = 1 := by simpa only [d366256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43337 p hg
    simpa only [d366256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43339 (p : Pattern) (guard : d366257 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d342996 p = 1 := by simpa only [d366257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43326 p hg
    simpa only [d366257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366256 p = 1 := by simpa only [d366257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43338 p hg
    simpa only [d366257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43340 (p : Pattern) (guard : d366258 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366250 p = 1 := by simpa only [d366258, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43321 p hg
    simpa only [d366258, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366257 p = 1 := by simpa only [d366258, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43339 p hg
    simpa only [d366258, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43341 (p : Pattern) (guard : d366259 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366251 p = 1 := by simpa only [d366259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43293 p hg
    simpa only [d366259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366258 p = 1 := by simpa only [d366259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43340 p hg
    simpa only [d366259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43342 (p : Pattern) (guard : d343012 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342918 p = 1 := by simpa only [d343012, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43240 p hg
    simpa only [d343012, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342793 p = 1 := by simpa only [d343012, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43057 p hg
    simpa only [d343012, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43343 (p : Pattern) (guard : d343013 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d343012 p = 1 := by simpa only [d343013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43342 p hg
    simpa only [d343013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342801 p = 1 := by simpa only [d343013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43069 p hg
    simpa only [d343013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43344 (p : Pattern) (guard : d366260 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366259 p = 1 := by simpa only [d366260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43341 p hg
    simpa only [d366260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343013 p = 1 := by simpa only [d366260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43343 p hg
    simpa only [d366260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43345 (p : Pattern) (guard : d366261 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366260 p = 1 := by simpa only [d366261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43344 p hg
    simpa only [d366261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43346 (p : Pattern) (guard : d366262 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d342929 p = 1 := by simpa only [d366262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43248 p hg
    simpa only [d366262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366261 p = 1 := by simpa only [d366262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43345 p hg
    simpa only [d366262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43347 (p : Pattern) (guard : d366229 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare43348 (p : Pattern) (guard : d366230 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366229 p = 1 := by simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43347 p hg
    simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43349 (p : Pattern) (guard : d366231 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366230 p = 1 := by simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43348 p hg
    simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43350 (p : Pattern) (guard : d366232 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366231 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43349 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342828 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43154 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43351 (p : Pattern) (guard : d342963 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare43352 (p : Pattern) (guard : d342964 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342963 p = 1 := by simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43351 p hg
    simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43353 (p : Pattern) (guard : d342965 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342964 p = 1 := by simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43352 p hg
    simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43354 (p : Pattern) (guard : d342966 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342965 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43353 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42960 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43355 (p : Pattern) (guard : d366233 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366232 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43350 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342966 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43354 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43356 (p : Pattern) (guard : d366234 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366233 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43355 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342830 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43156 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43357 (p : Pattern) (guard : d366235 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366234 p = 1 := by simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43356 p hg
    simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43358 (p : Pattern) (guard : d366236 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366235 p = 1 := by simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43357 p hg
    simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43359 (p : Pattern) (guard : d366237 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366236 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43358 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342833 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43159 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43360 (p : Pattern) (guard : d366238 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366237 p = 1 := by simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43359 p hg
    simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342834 p = 1 := by simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43160 p hg
    simpa only [d366238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43361 (p : Pattern) (guard : d366239 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366238 p = 1 := by simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43360 p hg
    simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43362 (p : Pattern) (guard : d366240 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366239 p = 1 := by simpa only [d366240, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43361 p hg
    simpa only [d366240, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366240, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366240, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43363 (p : Pattern) (guard : d366241 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366241, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366241, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366240 p = 1 := by simpa only [d366241, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43362 p hg
    simpa only [d366241, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43364 (p : Pattern) (guard : d366242 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366241 p = 1 := by simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43363 p hg
    simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342838 p = 1 := by simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43164 p hg
    simpa only [d366242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43365 (p : Pattern) (guard : d366243 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366242 p = 1 := by simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43364 p hg
    simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43366 (p : Pattern) (guard : d366244 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366243 p = 1 := by simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43365 p hg
    simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43367 (p : Pattern) (guard : d366252 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366244 p = 1 := by simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43366 p hg
    simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43368 (p : Pattern) (guard : d366253 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366252 p = 1 := by simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43367 p hg
    simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342858 p = 1 := by simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43168 p hg
    simpa only [d366253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43369 (p : Pattern) (guard : d366254 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366253 p = 1 := by simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43368 p hg
    simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43370 (p : Pattern) (guard : d342982 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43164 p hg
    simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43371 (p : Pattern) (guard : d342983 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342982 p = 1 := by simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43370 p hg
    simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43372 (p : Pattern) (guard : d342984 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342983 p = 1 := by simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43371 p hg
    simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43373 (p : Pattern) (guard : d343004 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342984 p = 1 := by simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43372 p hg
    simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43374 (p : Pattern) (guard : d343005 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343004 p = 1 := by simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43373 p hg
    simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43375 (p : Pattern) (guard : d343006 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d343005 p = 1 := by simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43374 p hg
    simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d343006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43376 (p : Pattern) (guard : d366255 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366254 p = 1 := by simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43369 p hg
    simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343006 p = 1 := by simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43375 p hg
    simpa only [d366255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43377 (p : Pattern) (guard : d366263 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366255 p = 1 := by simpa only [d366263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43376 p hg
    simpa only [d366263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43378 (p : Pattern) (guard : d366264 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366263 p = 1 := by simpa only [d366264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43377 p hg
    simpa only [d366264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43379 (p : Pattern) (guard : d366265 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366265, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366265, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366264 p = 1 := by simpa only [d366265, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43378 p hg
    simpa only [d366265, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43380 (p : Pattern) (guard : d366266 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366265 p = 1 := by simpa only [d366266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43379 p hg
    simpa only [d366266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43381 (p : Pattern) (guard : d342797 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342739 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42978 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43382 (p : Pattern) (guard : d342798 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342797 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43381 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43383 (p : Pattern) (guard : d342799 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342798 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43382 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43384 (p : Pattern) (guard : d342800 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342799 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43383 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43385 (p : Pattern) (guard : d343021 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342800 p = 1 := by simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43384 p hg
    simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43386 (p : Pattern) (guard : d343022 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343021 p = 1 := by simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43385 p hg
    simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43387 (p : Pattern) (guard : d366267 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366266 p = 1 := by simpa only [d366267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43380 p hg
    simpa only [d366267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343022 p = 1 := by simpa only [d366267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43386 p hg
    simpa only [d366267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43388 (p : Pattern) (guard : d366268 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366267 p = 1 := by simpa only [d366268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43387 p hg
    simpa only [d366268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43389 (p : Pattern) (guard : d366269 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366268 p = 1 := by simpa only [d366269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43388 p hg
    simpa only [d366269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43390 (p : Pattern) (guard : d366270 p = 1) : d51470 p ≤ (8 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d366262 p = 1 := by simpa only [d366270, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43346 p hg
    simpa only [d366270, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366269 p = 1 := by simpa only [d366270, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43389 p hg
    simpa only [d366270, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43391 (p : Pattern) (guard : d2001 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43182 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43392 (p : Pattern) (guard : d2002 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43391 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43393 (p : Pattern) (guard : d2005 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43182 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43394 (p : Pattern) (guard : d42940 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43393 p hg
    simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1085 p = 1 := by simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42999 p hg
    simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43395 (p : Pattern) (guard : d42941 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43392 p hg
    simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42940 p = 1 := by simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43394 p hg
    simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43396 (p : Pattern) (guard : d42942 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d42941 p = 1 := by simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43395 p hg
    simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43397 (p : Pattern) (guard : d42943 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d42942 p = 1 := by simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43396 p hg
    simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43398 (p : Pattern) (guard : d366224 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d42943 p = 1 := by simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43397 p hg
    simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342820 p = 1 := by simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43187 p hg
    simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43399 (p : Pattern) (guard : d366225 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366224 p = 1 := by simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43398 p hg
    simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342821 p = 1 := by simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43188 p hg
    simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43400 (p : Pattern) (guard : d366226 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366225 p = 1 := by simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43399 p hg
    simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43401 (p : Pattern) (guard : d366227 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366226 p = 1 := by simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43400 p hg
    simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342823 p = 1 := by simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43190 p hg
    simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43402 (p : Pattern) (guard : d366271 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366227 p = 1 := by simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43401 p hg
    simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43403 (p : Pattern) (guard : d366228 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare43404 (p : Pattern) (guard : d366272 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366271 p = 1 := by simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43402 p hg
    simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366228 p = 1 := by simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43403 p hg
    simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43405 (p : Pattern) (guard : d366229 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare43406 (p : Pattern) (guard : d366273 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366272 p = 1 := by simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43404 p hg
    simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366229 p = 1 := by simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43405 p hg
    simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43407 (p : Pattern) (guard : d366274 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366273 p = 1 := by simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43406 p hg
    simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43408 (p : Pattern) (guard : d366275 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366274 p = 1 := by simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43407 p hg
    simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342882 p = 1 := by simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43197 p hg
    simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43409 (p : Pattern) (guard : d342959 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342821 p = 1 := by simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43188 p hg
    simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43410 (p : Pattern) (guard : d342960 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342959 p = 1 := by simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43409 p hg
    simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43411 (p : Pattern) (guard : d342961 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342960 p = 1 := by simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43410 p hg
    simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342712 p = 1 := by simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43009 p hg
    simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43412 (p : Pattern) (guard : d343032 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342961 p = 1 := by simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43411 p hg
    simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43413 (p : Pattern) (guard : d342962 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare43414 (p : Pattern) (guard : d343033 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d343032 p = 1 := by simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43412 p hg
    simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342962 p = 1 := by simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43413 p hg
    simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43415 (p : Pattern) (guard : d342963 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare43416 (p : Pattern) (guard : d343034 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d343033 p = 1 := by simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43414 p hg
    simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342963 p = 1 := by simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43415 p hg
    simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43417 (p : Pattern) (guard : d343035 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d343034 p = 1 := by simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43416 p hg
    simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43418 (p : Pattern) (guard : d343036 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d343035 p = 1 := by simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43417 p hg
    simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342758 p = 1 := by simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43018 p hg
    simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43419 (p : Pattern) (guard : d366276 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366275 p = 1 := by simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43408 p hg
    simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343036 p = 1 := by simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43418 p hg
    simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43420 (p : Pattern) (guard : d366277 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366276 p = 1 := by simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43419 p hg
    simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342884 p = 1 := by simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43199 p hg
    simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43421 (p : Pattern) (guard : d366278 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366277 p = 1 := by simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43420 p hg
    simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43422 (p : Pattern) (guard : d366279 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366278 p = 1 := by simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43421 p hg
    simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43423 (p : Pattern) (guard : d366280 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366279 p = 1 := by simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43422 p hg
    simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342887 p = 1 := by simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43202 p hg
    simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43424 (p : Pattern) (guard : d366281 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366280 p = 1 := by simpa only [d366281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43423 p hg
    simpa only [d366281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342888 p = 1 := by simpa only [d366281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43203 p hg
    simpa only [d366281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43425 (p : Pattern) (guard : d366282 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366281 p = 1 := by simpa only [d366282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43424 p hg
    simpa only [d366282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43426 (p : Pattern) (guard : d366283 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366282 p = 1 := by simpa only [d366283, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43425 p hg
    simpa only [d366283, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366283, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d366283, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43427 (p : Pattern) (guard : d366284 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366284, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366284, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366283 p = 1 := by simpa only [d366284, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43426 p hg
    simpa only [d366284, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43428 (p : Pattern) (guard : d366285 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366284 p = 1 := by simpa only [d366285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43427 p hg
    simpa only [d366285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342892 p = 1 := by simpa only [d366285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43207 p hg
    simpa only [d366285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43429 (p : Pattern) (guard : d366286 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366285 p = 1 := by simpa only [d366286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43428 p hg
    simpa only [d366286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43430 (p : Pattern) (guard : d366287 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366286 p = 1 := by simpa only [d366287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43429 p hg
    simpa only [d366287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43431 (p : Pattern) (guard : d366288 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366287 p = 1 := by simpa only [d366288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43430 p hg
    simpa only [d366288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43432 (p : Pattern) (guard : d366289 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366288 p = 1 := by simpa only [d366289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43431 p hg
    simpa only [d366289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342896 p = 1 := by simpa only [d366289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43211 p hg
    simpa only [d366289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43433 (p : Pattern) (guard : d366290 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366289 p = 1 := by simpa only [d366290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43432 p hg
    simpa only [d366290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43434 (p : Pattern) (guard : d343052 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342892 p = 1 := by simpa only [d343052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43207 p hg
    simpa only [d343052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43435 (p : Pattern) (guard : d343053 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343052 p = 1 := by simpa only [d343053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43434 p hg
    simpa only [d343053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43436 (p : Pattern) (guard : d343054 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343053 p = 1 := by simpa only [d343054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43435 p hg
    simpa only [d343054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43437 (p : Pattern) (guard : d343055 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343054 p = 1 := by simpa only [d343055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43436 p hg
    simpa only [d343055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43438 (p : Pattern) (guard : d343056 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343055 p = 1 := by simpa only [d343056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43437 p hg
    simpa only [d343056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43439 (p : Pattern) (guard : d343057 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d343056 p = 1 := by simpa only [d343057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43438 p hg
    simpa only [d343057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43440 (p : Pattern) (guard : d366291 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366290 p = 1 := by simpa only [d366291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43433 p hg
    simpa only [d366291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343057 p = 1 := by simpa only [d366291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43439 p hg
    simpa only [d366291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43441 (p : Pattern) (guard : d366292 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366291 p = 1 := by simpa only [d366292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43440 p hg
    simpa only [d366292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43442 (p : Pattern) (guard : d366293 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366292 p = 1 := by simpa only [d366293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43441 p hg
    simpa only [d366293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43443 (p : Pattern) (guard : d366294 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366294, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366294, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366293 p = 1 := by simpa only [d366294, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43442 p hg
    simpa only [d366294, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43444 (p : Pattern) (guard : d366295 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366294 p = 1 := by simpa only [d366295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43443 p hg
    simpa only [d366295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43445 (p : Pattern) (guard : d343063 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342773 p = 1 := by simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43036 p hg
    simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43446 (p : Pattern) (guard : d343064 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343063 p = 1 := by simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43445 p hg
    simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43447 (p : Pattern) (guard : d343065 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343064 p = 1 := by simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43446 p hg
    simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43448 (p : Pattern) (guard : d343066 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343065 p = 1 := by simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43447 p hg
    simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43449 (p : Pattern) (guard : d343067 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343066 p = 1 := by simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43448 p hg
    simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43450 (p : Pattern) (guard : d343068 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343067 p = 1 := by simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43449 p hg
    simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43451 (p : Pattern) (guard : d366296 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366295 p = 1 := by simpa only [d366296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43444 p hg
    simpa only [d366296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343068 p = 1 := by simpa only [d366296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43450 p hg
    simpa only [d366296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43452 (p : Pattern) (guard : d366297 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366296 p = 1 := by simpa only [d366297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43451 p hg
    simpa only [d366297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43453 (p : Pattern) (guard : d366298 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366297 p = 1 := by simpa only [d366298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43452 p hg
    simpa only [d366298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43454 (p : Pattern) (guard : d366299 p = 1) : d51634 p ≤ (8 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d366298 p = 1 := by simpa only [d366299, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43453 p hg
    simpa only [d366299, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366299, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d366299, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43455 (p : Pattern) (guard : d366300 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d366270 p = 1 := by simpa only [d366300, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43390 p hg
    simpa only [d366300, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366299 p = 1 := by simpa only [d366300, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43454 p hg
    simpa only [d366300, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43456 (p : Pattern) (guard : d366301 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366300 p = 1 := by simpa only [d366301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43455 p hg
    simpa only [d366301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43457 (p : Pattern) (guard : d366302 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366301 p = 1 := by simpa only [d366302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43456 p hg
    simpa only [d366302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43458 (p : Pattern) (guard : d366303 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366302 p = 1 := by simpa only [d366303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43457 p hg
    simpa only [d366303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43459 (p : Pattern) (guard : d366304 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366303 p = 1 := by simpa only [d366304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43458 p hg
    simpa only [d366304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43460 (p : Pattern) (guard : d366305 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366304 p = 1 := by simpa only [d366305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43459 p hg
    simpa only [d366305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43461 (p : Pattern) (guard : d366306 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366305 p = 1 := by simpa only [d366306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43460 p hg
    simpa only [d366306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43462 (p : Pattern) (guard : d366307 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d342914 p = 1 := by simpa only [d366307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43229 p hg
    simpa only [d366307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366306 p = 1 := by simpa only [d366307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43461 p hg
    simpa only [d366307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43463 (p : Pattern) (guard : d343081 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43092 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43464 (p : Pattern) (guard : d366308 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366237 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43273 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343081 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43463 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43465 (p : Pattern) (guard : d366309 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366308 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43464 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43466 (p : Pattern) (guard : d366310 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366309 p = 1 := by simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43465 p hg
    simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43467 (p : Pattern) (guard : d366311 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366310 p = 1 := by simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43466 p hg
    simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43468 (p : Pattern) (guard : d343086 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d343081 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43463 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43469 (p : Pattern) (guard : d343087 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d343086 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43468 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43470 (p : Pattern) (guard : d343088 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d343087 p = 1 := by simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43469 p hg
    simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43471 (p : Pattern) (guard : d343089 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343088 p = 1 := by simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43470 p hg
    simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43472 (p : Pattern) (guard : d366312 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43467 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343089 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43471 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43473 (p : Pattern) (guard : d366313 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366312 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43472 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43474 (p : Pattern) (guard : d366314 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366313 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43473 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43475 (p : Pattern) (guard : d366315 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366314 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43474 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43476 (p : Pattern) (guard : d343094 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343089 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43471 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43477 (p : Pattern) (guard : d343095 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343094 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43476 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43478 (p : Pattern) (guard : d343096 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343095 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43477 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43479 (p : Pattern) (guard : d343097 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343096 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43478 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43480 (p : Pattern) (guard : d366316 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366315 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43475 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343097 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43479 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43481 (p : Pattern) (guard : d366317 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366316 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43480 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43482 (p : Pattern) (guard : d366318 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366317 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43481 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43483 (p : Pattern) (guard : d366319 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366318 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43482 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43484 (p : Pattern) (guard : d366320 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366319 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43483 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43485 (p : Pattern) (guard : d366321 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366320 p = 1 := by simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43484 p hg
    simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43486 (p : Pattern) (guard : d366322 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366321 p = 1 := by simpa only [d366322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43485 p hg
    simpa only [d366322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43487 (p : Pattern) (guard : d366323 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366322 p = 1 := by simpa only [d366323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43486 p hg
    simpa only [d366323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43488 (p : Pattern) (guard : d366311 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366310 p = 1 := by simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43466 p hg
    simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43489 (p : Pattern) (guard : d343089 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343088 p = 1 := by simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43470 p hg
    simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43490 (p : Pattern) (guard : d366312 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43488 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343089 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43489 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43491 (p : Pattern) (guard : d366313 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366312 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43490 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43492 (p : Pattern) (guard : d366314 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366313 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43491 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43493 (p : Pattern) (guard : d366315 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366314 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43492 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43494 (p : Pattern) (guard : d343094 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343089 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43489 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43495 (p : Pattern) (guard : d343095 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343094 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43494 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43496 (p : Pattern) (guard : d343096 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343095 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43495 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43497 (p : Pattern) (guard : d343097 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343096 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43496 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43498 (p : Pattern) (guard : d366316 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366315 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43493 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343097 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43497 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43499 (p : Pattern) (guard : d366317 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366316 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43498 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
