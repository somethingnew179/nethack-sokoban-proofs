import NetHack.Soko22Hazard87.Compare008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2250 (p : Pattern) (guard : d54918 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54917 p = 1 := by simpa only [d54918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2249 p hg
    simpa only [d54918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2251 (p : Pattern) (guard : d54919 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54918 p = 1 := by simpa only [d54919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2250 p hg
    simpa only [d54919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2252 (p : Pattern) (guard : d54920 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d54908 p = 1 := by simpa only [d54920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d54920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54919 p = 1 := by simpa only [d54920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2251 p hg
    simpa only [d54920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2253 (p : Pattern) (guard : d53793 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2254 (p : Pattern) (guard : d54921 p = 1) : d48081 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53793 p = 1 := by simpa only [d54921, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2253 p hg
    simpa only [d54921, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54921, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d54921, d48081, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2255 (p : Pattern) (guard : d54922 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d54921 p = 1 := by simpa only [d54922, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d54922, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54922, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d54922, d48083, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2256 (p : Pattern) (guard : d54923 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54922 p = 1 := by simpa only [d54923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2255 p hg
    simpa only [d54923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2257 (p : Pattern) (guard : d54924 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54923 p = 1 := by simpa only [d54924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2256 p hg
    simpa only [d54924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2258 (p : Pattern) (guard : d54925 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54924 p = 1 := by simpa only [d54925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d54925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2259 (p : Pattern) (guard : d54926 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54925 p = 1 := by simpa only [d54926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2258 p hg
    simpa only [d54926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2260 (p : Pattern) (guard : d54927 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54926 p = 1 := by simpa only [d54927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2259 p hg
    simpa only [d54927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2261 (p : Pattern) (guard : d54928 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54927 p = 1 := by simpa only [d54928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2260 p hg
    simpa only [d54928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2262 (p : Pattern) (guard : d54929 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54928 p = 1 := by simpa only [d54929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2261 p hg
    simpa only [d54929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2263 (p : Pattern) (guard : d54930 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54929 p = 1 := by simpa only [d54930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2262 p hg
    simpa only [d54930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2264 (p : Pattern) (guard : d54931 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54930 p = 1 := by simpa only [d54931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2263 p hg
    simpa only [d54931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2265 (p : Pattern) (guard : d54932 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54931 p = 1 := by simpa only [d54932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2264 p hg
    simpa only [d54932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2266 (p : Pattern) (guard : d54933 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d54920 p = 1 := by simpa only [d54933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2252 p hg
    simpa only [d54933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54932 p = 1 := by simpa only [d54933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2265 p hg
    simpa only [d54933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2267 (p : Pattern) (guard : d54934 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 260 with
  | false =>
    have hg : d54933 p = 1 := by simpa only [d54934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2266 p hg
    simpa only [d54934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2268 (p : Pattern) (guard : d54935 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 259 with
  | false =>
    have hg : d54934 p = 1 := by simpa only [d54935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2267 p hg
    simpa only [d54935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2269 (p : Pattern) (guard : d54936 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 258 with
  | false =>
    have hg : d54935 p = 1 := by simpa only [d54936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2268 p hg
    simpa only [d54936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2270 (p : Pattern) (guard : d54937 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 257 with
  | false =>
    have hg : d54936 p = 1 := by simpa only [d54937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2269 p hg
    simpa only [d54937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2271 (p : Pattern) (guard : d54938 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 256 with
  | false =>
    have hg : d54937 p = 1 := by simpa only [d54938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2270 p hg
    simpa only [d54938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2272 (p : Pattern) (guard : d54939 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 255 with
  | false =>
    have hg : d54938 p = 1 := by simpa only [d54939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2271 p hg
    simpa only [d54939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2273 (p : Pattern) (guard : d54940 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 254 with
  | false =>
    have hg : d54939 p = 1 := by simpa only [d54940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2272 p hg
    simpa only [d54940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2274 (p : Pattern) (guard : d54941 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 253 with
  | false =>
    have hg : d54940 p = 1 := by simpa only [d54941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d54941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2275 (p : Pattern) (guard : d54942 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 252 with
  | false =>
    have hg : d54941 p = 1 := by simpa only [d54942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2274 p hg
    simpa only [d54942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2276 (p : Pattern) (guard : d54943 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 251 with
  | false =>
    have hg : d54942 p = 1 := by simpa only [d54943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2275 p hg
    simpa only [d54943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2277 (p : Pattern) (guard : d54944 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 250 with
  | false =>
    have hg : d54943 p = 1 := by simpa only [d54944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d54944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2278 (p : Pattern) (guard : d54945 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 249 with
  | false =>
    have hg : d54944 p = 1 := by simpa only [d54945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2277 p hg
    simpa only [d54945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2279 (p : Pattern) (guard : d54946 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 245 with
  | false =>
    have hg : d54945 p = 1 := by simpa only [d54946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2278 p hg
    simpa only [d54946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2280 (p : Pattern) (guard : d54947 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 200 with
  | false =>
    have hg : d54946 p = 1 := by simpa only [d54947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2279 p hg
    simpa only [d54947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2281 (p : Pattern) (guard : d54948 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 199 with
  | false =>
    have hg : d54947 p = 1 := by simpa only [d54948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2280 p hg
    simpa only [d54948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2282 (p : Pattern) (guard : d54949 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 186 with
  | false =>
    have hg : d54948 p = 1 := by simpa only [d54949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2281 p hg
    simpa only [d54949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2283 (p : Pattern) (guard : d54950 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 185 with
  | false =>
    have hg : d54949 p = 1 := by simpa only [d54950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2282 p hg
    simpa only [d54950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2284 (p : Pattern) (guard : d54951 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 184 with
  | false =>
    have hg : d54950 p = 1 := by simpa only [d54951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2283 p hg
    simpa only [d54951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2285 (p : Pattern) (guard : d54952 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 181 with
  | false =>
    have hg : d54951 p = 1 := by simpa only [d54952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2284 p hg
    simpa only [d54952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2286 (p : Pattern) (guard : d54953 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 177 with
  | false =>
    have hg : d54952 p = 1 := by simpa only [d54953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2285 p hg
    simpa only [d54953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2287 (p : Pattern) (guard : d54954 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 164 with
  | false =>
    have hg : d54953 p = 1 := by simpa only [d54954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2286 p hg
    simpa only [d54954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2288 (p : Pattern) (guard : d54955 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 156 with
  | false =>
    have hg : d54954 p = 1 := by simpa only [d54955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2287 p hg
    simpa only [d54955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2289 (p : Pattern) (guard : d54956 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 155 with
  | false =>
    have hg : d54955 p = 1 := by simpa only [d54956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2288 p hg
    simpa only [d54956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2290 (p : Pattern) (guard : d54957 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 134 with
  | false =>
    have hg : d54956 p = 1 := by simpa only [d54957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2289 p hg
    simpa only [d54957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2291 (p : Pattern) (guard : d54958 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 133 with
  | false =>
    have hg : d54957 p = 1 := by simpa only [d54958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2290 p hg
    simpa only [d54958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2292 (p : Pattern) (guard : d54959 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 120 with
  | false =>
    have hg : d54958 p = 1 := by simpa only [d54959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2291 p hg
    simpa only [d54959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2293 (p : Pattern) (guard : d54960 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 118 with
  | false =>
    have hg : d54959 p = 1 := by simpa only [d54960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2292 p hg
    simpa only [d54960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2294 (p : Pattern) (guard : d54961 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 114 with
  | false =>
    have hg : d54960 p = 1 := by simpa only [d54961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2293 p hg
    simpa only [d54961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2295 (p : Pattern) (guard : d54962 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 111 with
  | false =>
    have hg : d54961 p = 1 := by simpa only [d54962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2294 p hg
    simpa only [d54962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2296 (p : Pattern) (guard : d54963 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 98 with
  | false =>
    have hg : d54962 p = 1 := by simpa only [d54963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2295 p hg
    simpa only [d54963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2297 (p : Pattern) (guard : d54964 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 97 with
  | false =>
    have hg : d54963 p = 1 := by simpa only [d54964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2296 p hg
    simpa only [d54964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2298 (p : Pattern) (guard : d54965 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 94 with
  | false =>
    have hg : d54964 p = 1 := by simpa only [d54965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2297 p hg
    simpa only [d54965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2299 (p : Pattern) (guard : d54966 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 76 with
  | false =>
    have hg : d54965 p = 1 := by simpa only [d54966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2298 p hg
    simpa only [d54966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2300 (p : Pattern) (guard : d54967 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 67 with
  | false =>
    have hg : d54966 p = 1 := by simpa only [d54967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2299 p hg
    simpa only [d54967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2301 (p : Pattern) (guard : d54968 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 52 with
  | false =>
    have hg : d54967 p = 1 := by simpa only [d54968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2300 p hg
    simpa only [d54968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2302 (p : Pattern) (guard : d54969 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 47 with
  | false =>
    have hg : d54968 p = 1 := by simpa only [d54969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2301 p hg
    simpa only [d54969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2303 (p : Pattern) (guard : d54970 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 46 with
  | false =>
    have hg : d54969 p = 1 := by simpa only [d54970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2302 p hg
    simpa only [d54970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2304 (p : Pattern) (guard : d54971 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 45 with
  | false =>
    have hg : d54970 p = 1 := by simpa only [d54971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2303 p hg
    simpa only [d54971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2305 (p : Pattern) (guard : d54972 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 30 with
  | false =>
    have hg : d54971 p = 1 := by simpa only [d54972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2304 p hg
    simpa only [d54972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2306 (p : Pattern) (guard : d54973 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 29 with
  | false =>
    have hg : d54972 p = 1 := by simpa only [d54973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2305 p hg
    simpa only [d54973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2307 (p : Pattern) (guard : d54974 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 28 with
  | false =>
    have hg : d54973 p = 1 := by simpa only [d54974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2306 p hg
    simpa only [d54974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2308 (p : Pattern) (guard : d54975 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 27 with
  | false =>
    have hg : d54974 p = 1 := by simpa only [d54975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2307 p hg
    simpa only [d54975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2309 (p : Pattern) (guard : d54976 p = 1) : d48083 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 25 with
  | false =>
    have hg : d54975 p = 1 := by simpa only [d54976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2308 p hg
    simpa only [d54976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d54976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2310 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-1 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2311 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-2 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2312 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (0 : Int) + d47768 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2313 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-1 : Int) + d47768 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2314 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2315 (p : Pattern) (guard : d0 p = 1) : d48083 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2316 (p : Pattern) (guard : d64791 p = 1) : d47911 p ≤ (0 : Int) + d47911 p := by
  omega
theorem compare2317 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2318 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2319 (p : Pattern) (guard : d103 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2320 (p : Pattern) (guard : d0 p = 1) : d47766 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2321 (p : Pattern) (guard : d213 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2322 (p : Pattern) (guard : d2525 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d213 p = 1 := by simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2321 p hg
    simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2323 (p : Pattern) (guard : d2526 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2525 p = 1 := by simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2322 p hg
    simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2324 (p : Pattern) (guard : d2527 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2526 p = 1 := by simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2323 p hg
    simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2325 (p : Pattern) (guard : d2528 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2527 p = 1 := by simpa only [d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2324 p hg
    simpa only [d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2326 (p : Pattern) (guard : d55348 p = 1) : d47768 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55348, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d55348, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2528 p = 1 := by simpa only [d55348, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2325 p hg
    simpa only [d55348, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2327 (p : Pattern) (guard : d0 p = 1) : d47910 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2328 (p : Pattern) (guard : d55349 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 48 with
  | false =>
    have hg : d55348 p = 1 := by simpa only [d55349, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2326 p hg
    simpa only [d55349, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55349, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d55349, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2329 (p : Pattern) (guard : d55350 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55349 p = 1 := by simpa only [d55350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2328 p hg
    simpa only [d55350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2330 (p : Pattern) (guard : d55351 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55350 p = 1 := by simpa only [d55351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2329 p hg
    simpa only [d55351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2331 (p : Pattern) (guard : d55352 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55351 p = 1 := by simpa only [d55352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2330 p hg
    simpa only [d55352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2332 (p : Pattern) (guard : d55353 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55352 p = 1 := by simpa only [d55353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2331 p hg
    simpa only [d55353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2333 (p : Pattern) (guard : d55354 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55353 p = 1 := by simpa only [d55354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2332 p hg
    simpa only [d55354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2334 (p : Pattern) (guard : d283 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2335 (p : Pattern) (guard : d2536 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2334 p hg
    simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2336 (p : Pattern) (guard : d2537 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2536 p = 1 := by simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2335 p hg
    simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2337 (p : Pattern) (guard : d2538 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2537 p = 1 := by simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2336 p hg
    simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2338 (p : Pattern) (guard : d2539 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2538 p = 1 := by simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2337 p hg
    simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2339 (p : Pattern) (guard : d2540 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2539 p = 1 := by simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2338 p hg
    simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2340 (p : Pattern) (guard : d55355 p = 1) : d47768 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55355, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d55355, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2540 p = 1 := by simpa only [d55355, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2339 p hg
    simpa only [d55355, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2341 (p : Pattern) (guard : d55356 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 48 with
  | false =>
    have hg : d55355 p = 1 := by simpa only [d55356, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2340 p hg
    simpa only [d55356, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55356, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d55356, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2342 (p : Pattern) (guard : d55357 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55356 p = 1 := by simpa only [d55357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2341 p hg
    simpa only [d55357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2343 (p : Pattern) (guard : d55358 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55357 p = 1 := by simpa only [d55358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2342 p hg
    simpa only [d55358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2344 (p : Pattern) (guard : d55359 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55358 p = 1 := by simpa only [d55359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2343 p hg
    simpa only [d55359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2345 (p : Pattern) (guard : d55360 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55359 p = 1 := by simpa only [d55360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2344 p hg
    simpa only [d55360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2346 (p : Pattern) (guard : d55361 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55360 p = 1 := by simpa only [d55361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2345 p hg
    simpa only [d55361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2347 (p : Pattern) (guard : d55362 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d55354 p = 1 := by simpa only [d55362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d55362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55361 p = 1 := by simpa only [d55362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2346 p hg
    simpa only [d55362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2348 (p : Pattern) (guard : d496 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2349 (p : Pattern) (guard : d2549 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d496 p = 1 := by simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2350 (p : Pattern) (guard : d2550 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2549 p = 1 := by simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2349 p hg
    simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2351 (p : Pattern) (guard : d2551 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2550 p = 1 := by simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2352 (p : Pattern) (guard : d2552 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2551 p = 1 := by simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2353 (p : Pattern) (guard : d2553 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2552 p = 1 := by simpa only [d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2354 (p : Pattern) (guard : d55363 p = 1) : d47768 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55363, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d55363, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2553 p = 1 := by simpa only [d55363, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d55363, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2355 (p : Pattern) (guard : d55364 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 48 with
  | false =>
    have hg : d55363 p = 1 := by simpa only [d55364, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2354 p hg
    simpa only [d55364, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55364, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d55364, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2356 (p : Pattern) (guard : d55365 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55364 p = 1 := by simpa only [d55365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d55365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2357 (p : Pattern) (guard : d55366 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55365 p = 1 := by simpa only [d55366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2356 p hg
    simpa only [d55366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2358 (p : Pattern) (guard : d55367 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55366 p = 1 := by simpa only [d55367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2357 p hg
    simpa only [d55367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2359 (p : Pattern) (guard : d55368 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55367 p = 1 := by simpa only [d55368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2358 p hg
    simpa only [d55368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2360 (p : Pattern) (guard : d55369 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55368 p = 1 := by simpa only [d55369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2359 p hg
    simpa only [d55369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2361 (p : Pattern) (guard : d55370 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55369 p = 1 := by simpa only [d55370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2360 p hg
    simpa only [d55370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2362 (p : Pattern) (guard : d55371 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d55362 p = 1 := by simpa only [d55371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d55371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55370 p = 1 := by simpa only [d55371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d55371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2363 (p : Pattern) (guard : d788 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2364 (p : Pattern) (guard : d2563 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d788 p = 1 := by simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2365 (p : Pattern) (guard : d2564 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2563 p = 1 := by simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2366 (p : Pattern) (guard : d2565 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2564 p = 1 := by simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2365 p hg
    simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2367 (p : Pattern) (guard : d2566 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2565 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2366 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2368 (p : Pattern) (guard : d2567 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2566 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2369 (p : Pattern) (guard : d55372 p = 1) : d47768 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55372, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d55372, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2567 p = 1 := by simpa only [d55372, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d55372, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2370 (p : Pattern) (guard : d55373 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 48 with
  | false =>
    have hg : d55372 p = 1 := by simpa only [d55373, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2369 p hg
    simpa only [d55373, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55373, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d55373, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2371 (p : Pattern) (guard : d55374 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55373 p = 1 := by simpa only [d55374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d55374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2372 (p : Pattern) (guard : d55375 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55374 p = 1 := by simpa only [d55375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d55375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2373 (p : Pattern) (guard : d55376 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55375 p = 1 := by simpa only [d55376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2372 p hg
    simpa only [d55376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2374 (p : Pattern) (guard : d55377 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55376 p = 1 := by simpa only [d55377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2373 p hg
    simpa only [d55377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2375 (p : Pattern) (guard : d55378 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55377 p = 1 := by simpa only [d55378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2374 p hg
    simpa only [d55378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2376 (p : Pattern) (guard : d55379 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55378 p = 1 := by simpa only [d55379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d55379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2377 (p : Pattern) (guard : d55380 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55379 p = 1 := by simpa only [d55380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2376 p hg
    simpa only [d55380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2378 (p : Pattern) (guard : d55381 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d55371 p = 1 := by simpa only [d55381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2362 p hg
    simpa only [d55381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55380 p = 1 := by simpa only [d55381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d55381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2379 (p : Pattern) (guard : d1167 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2380 (p : Pattern) (guard : d2578 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2381 (p : Pattern) (guard : d2579 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2578 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2380 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2382 (p : Pattern) (guard : d2580 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2579 p = 1 := by simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2381 p hg
    simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2383 (p : Pattern) (guard : d2581 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2580 p = 1 := by simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2382 p hg
    simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2384 (p : Pattern) (guard : d2582 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2581 p = 1 := by simpa only [d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2383 p hg
    simpa only [d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2385 (p : Pattern) (guard : d55382 p = 1) : d47768 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55382, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d55382, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2582 p = 1 := by simpa only [d55382, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2384 p hg
    simpa only [d55382, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2386 (p : Pattern) (guard : d55383 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 48 with
  | false =>
    have hg : d55382 p = 1 := by simpa only [d55383, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d55383, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55383, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d55383, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2387 (p : Pattern) (guard : d55384 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55383 p = 1 := by simpa only [d55384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2386 p hg
    simpa only [d55384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2388 (p : Pattern) (guard : d55385 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55384 p = 1 := by simpa only [d55385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2387 p hg
    simpa only [d55385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2389 (p : Pattern) (guard : d55386 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55385 p = 1 := by simpa only [d55386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d55386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2390 (p : Pattern) (guard : d55387 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55386 p = 1 := by simpa only [d55387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2389 p hg
    simpa only [d55387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2391 (p : Pattern) (guard : d55388 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55387 p = 1 := by simpa only [d55388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2390 p hg
    simpa only [d55388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2392 (p : Pattern) (guard : d55389 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55388 p = 1 := by simpa only [d55389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2391 p hg
    simpa only [d55389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2393 (p : Pattern) (guard : d55390 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55389 p = 1 := by simpa only [d55390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2392 p hg
    simpa only [d55390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2394 (p : Pattern) (guard : d55391 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55390 p = 1 := by simpa only [d55391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2393 p hg
    simpa only [d55391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2395 (p : Pattern) (guard : d55392 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d55381 p = 1 := by simpa only [d55392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d55392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55391 p = 1 := by simpa only [d55392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2394 p hg
    simpa only [d55392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2396 (p : Pattern) (guard : d1628 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2397 (p : Pattern) (guard : d2594 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1628 p = 1 := by simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2398 (p : Pattern) (guard : d2595 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2594 p = 1 := by simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2399 (p : Pattern) (guard : d2596 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2595 p = 1 := by simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2398 p hg
    simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2400 (p : Pattern) (guard : d2597 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2596 p = 1 := by simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2401 (p : Pattern) (guard : d2598 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2597 p = 1 := by simpa only [d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2402 (p : Pattern) (guard : d55393 p = 1) : d47768 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55393, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d55393, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2598 p = 1 := by simpa only [d55393, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2401 p hg
    simpa only [d55393, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2403 (p : Pattern) (guard : d55394 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 48 with
  | false =>
    have hg : d55393 p = 1 := by simpa only [d55394, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2402 p hg
    simpa only [d55394, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55394, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d55394, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2404 (p : Pattern) (guard : d55395 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55394 p = 1 := by simpa only [d55395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2403 p hg
    simpa only [d55395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2405 (p : Pattern) (guard : d55396 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55395 p = 1 := by simpa only [d55396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2404 p hg
    simpa only [d55396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2406 (p : Pattern) (guard : d55397 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55396 p = 1 := by simpa only [d55397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2405 p hg
    simpa only [d55397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2407 (p : Pattern) (guard : d55398 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55397 p = 1 := by simpa only [d55398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2406 p hg
    simpa only [d55398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2408 (p : Pattern) (guard : d55399 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55398 p = 1 := by simpa only [d55399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2407 p hg
    simpa only [d55399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2409 (p : Pattern) (guard : d55400 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55399 p = 1 := by simpa only [d55400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2408 p hg
    simpa only [d55400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2410 (p : Pattern) (guard : d55401 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55400 p = 1 := by simpa only [d55401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2409 p hg
    simpa only [d55401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2411 (p : Pattern) (guard : d55402 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55401 p = 1 := by simpa only [d55402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d55402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2412 (p : Pattern) (guard : d55403 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55402 p = 1 := by simpa only [d55403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d55403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2413 (p : Pattern) (guard : d55404 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d55392 p = 1 := by simpa only [d55404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d55404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55403 p = 1 := by simpa only [d55404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2412 p hg
    simpa only [d55404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2414 (p : Pattern) (guard : d2111 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2415 (p : Pattern) (guard : d2611 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d2111 p = 1 := by simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2416 (p : Pattern) (guard : d2612 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2611 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2417 (p : Pattern) (guard : d2613 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2612 p = 1 := by simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2416 p hg
    simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2418 (p : Pattern) (guard : d2614 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2613 p = 1 := by simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2419 (p : Pattern) (guard : d2615 p = 1) : d47767 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2614 p = 1 := by simpa only [d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2418 p hg
    simpa only [d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2420 (p : Pattern) (guard : d55405 p = 1) : d47768 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55405, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d55405, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2615 p = 1 := by simpa only [d55405, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d55405, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2421 (p : Pattern) (guard : d55406 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 48 with
  | false =>
    have hg : d55405 p = 1 := by simpa only [d55406, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2420 p hg
    simpa only [d55406, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55406, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d55406, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2422 (p : Pattern) (guard : d55407 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55406 p = 1 := by simpa only [d55407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d55407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2423 (p : Pattern) (guard : d55408 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55407 p = 1 := by simpa only [d55408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2422 p hg
    simpa only [d55408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2424 (p : Pattern) (guard : d55409 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55408 p = 1 := by simpa only [d55409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2423 p hg
    simpa only [d55409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2425 (p : Pattern) (guard : d55410 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55409 p = 1 := by simpa only [d55410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2424 p hg
    simpa only [d55410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2426 (p : Pattern) (guard : d55411 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55410 p = 1 := by simpa only [d55411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2425 p hg
    simpa only [d55411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2427 (p : Pattern) (guard : d55412 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55411 p = 1 := by simpa only [d55412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2426 p hg
    simpa only [d55412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2428 (p : Pattern) (guard : d55413 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55412 p = 1 := by simpa only [d55413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2427 p hg
    simpa only [d55413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2429 (p : Pattern) (guard : d55414 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55413 p = 1 := by simpa only [d55414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2428 p hg
    simpa only [d55414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2430 (p : Pattern) (guard : d55415 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55414 p = 1 := by simpa only [d55415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d55415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2431 (p : Pattern) (guard : d55416 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d55416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55415 p = 1 := by simpa only [d55416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2430 p hg
    simpa only [d55416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2432 (p : Pattern) (guard : d55417 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d55404 p = 1 := by simpa only [d55417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2413 p hg
    simpa only [d55417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55416 p = 1 := by simpa only [d55417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2431 p hg
    simpa only [d55417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2433 (p : Pattern) (guard : d55418 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 260 with
  | false =>
    have hg : d55417 p = 1 := by simpa only [d55418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d55418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2434 (p : Pattern) (guard : d55419 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 259 with
  | false =>
    have hg : d55418 p = 1 := by simpa only [d55419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2433 p hg
    simpa only [d55419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2435 (p : Pattern) (guard : d55420 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 258 with
  | false =>
    have hg : d55419 p = 1 := by simpa only [d55420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2434 p hg
    simpa only [d55420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2436 (p : Pattern) (guard : d55421 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 257 with
  | false =>
    have hg : d55420 p = 1 := by simpa only [d55421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2435 p hg
    simpa only [d55421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2437 (p : Pattern) (guard : d55422 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 256 with
  | false =>
    have hg : d55421 p = 1 := by simpa only [d55422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2436 p hg
    simpa only [d55422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2438 (p : Pattern) (guard : d55423 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 255 with
  | false =>
    have hg : d55422 p = 1 := by simpa only [d55423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2437 p hg
    simpa only [d55423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2439 (p : Pattern) (guard : d55424 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 254 with
  | false =>
    have hg : d55423 p = 1 := by simpa only [d55424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2438 p hg
    simpa only [d55424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2440 (p : Pattern) (guard : d55425 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 253 with
  | false =>
    have hg : d55424 p = 1 := by simpa only [d55425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2439 p hg
    simpa only [d55425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2441 (p : Pattern) (guard : d55426 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 252 with
  | false =>
    have hg : d55425 p = 1 := by simpa only [d55426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d55426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2442 (p : Pattern) (guard : d55427 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 251 with
  | false =>
    have hg : d55426 p = 1 := by simpa only [d55427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2441 p hg
    simpa only [d55427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2443 (p : Pattern) (guard : d55428 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 250 with
  | false =>
    have hg : d55427 p = 1 := by simpa only [d55428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2442 p hg
    simpa only [d55428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2444 (p : Pattern) (guard : d55429 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 249 with
  | false =>
    have hg : d55428 p = 1 := by simpa only [d55429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2443 p hg
    simpa only [d55429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2445 (p : Pattern) (guard : d55430 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 245 with
  | false =>
    have hg : d55429 p = 1 := by simpa only [d55430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2444 p hg
    simpa only [d55430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2446 (p : Pattern) (guard : d55431 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 200 with
  | false =>
    have hg : d55430 p = 1 := by simpa only [d55431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d55431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2447 (p : Pattern) (guard : d55432 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 199 with
  | false =>
    have hg : d55431 p = 1 := by simpa only [d55432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2446 p hg
    simpa only [d55432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2448 (p : Pattern) (guard : d55433 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 186 with
  | false =>
    have hg : d55432 p = 1 := by simpa only [d55433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2447 p hg
    simpa only [d55433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2449 (p : Pattern) (guard : d55434 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 185 with
  | false =>
    have hg : d55433 p = 1 := by simpa only [d55434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2448 p hg
    simpa only [d55434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2450 (p : Pattern) (guard : d55435 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 184 with
  | false =>
    have hg : d55434 p = 1 := by simpa only [d55435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2449 p hg
    simpa only [d55435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2451 (p : Pattern) (guard : d55436 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 181 with
  | false =>
    have hg : d55435 p = 1 := by simpa only [d55436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d55436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2452 (p : Pattern) (guard : d55437 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 177 with
  | false =>
    have hg : d55436 p = 1 := by simpa only [d55437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2451 p hg
    simpa only [d55437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2453 (p : Pattern) (guard : d55438 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 164 with
  | false =>
    have hg : d55437 p = 1 := by simpa only [d55438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2452 p hg
    simpa only [d55438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2454 (p : Pattern) (guard : d55439 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 156 with
  | false =>
    have hg : d55438 p = 1 := by simpa only [d55439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2453 p hg
    simpa only [d55439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2455 (p : Pattern) (guard : d55440 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 155 with
  | false =>
    have hg : d55439 p = 1 := by simpa only [d55440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d55440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2456 (p : Pattern) (guard : d55441 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d55440 p = 1 := by simpa only [d55441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2455 p hg
    simpa only [d55441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2457 (p : Pattern) (guard : d55442 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d55441 p = 1 := by simpa only [d55442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d55442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2458 (p : Pattern) (guard : d55443 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 120 with
  | false =>
    have hg : d55442 p = 1 := by simpa only [d55443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2457 p hg
    simpa only [d55443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2459 (p : Pattern) (guard : d55444 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 118 with
  | false =>
    have hg : d55443 p = 1 := by simpa only [d55444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2458 p hg
    simpa only [d55444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2460 (p : Pattern) (guard : d55445 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 114 with
  | false =>
    have hg : d55444 p = 1 := by simpa only [d55445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2459 p hg
    simpa only [d55445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2461 (p : Pattern) (guard : d55446 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 111 with
  | false =>
    have hg : d55445 p = 1 := by simpa only [d55446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d55446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2462 (p : Pattern) (guard : d55447 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 98 with
  | false =>
    have hg : d55446 p = 1 := by simpa only [d55447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2461 p hg
    simpa only [d55447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2463 (p : Pattern) (guard : d55448 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 97 with
  | false =>
    have hg : d55447 p = 1 := by simpa only [d55448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2462 p hg
    simpa only [d55448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2464 (p : Pattern) (guard : d55449 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 94 with
  | false =>
    have hg : d55448 p = 1 := by simpa only [d55449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d55449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2465 (p : Pattern) (guard : d55450 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 76 with
  | false =>
    have hg : d55449 p = 1 := by simpa only [d55450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2464 p hg
    simpa only [d55450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2466 (p : Pattern) (guard : d55451 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 67 with
  | false =>
    have hg : d55450 p = 1 := by simpa only [d55451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2465 p hg
    simpa only [d55451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2467 (p : Pattern) (guard : d55452 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 52 with
  | false =>
    have hg : d55451 p = 1 := by simpa only [d55452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2466 p hg
    simpa only [d55452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2468 (p : Pattern) (guard : d55453 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 47 with
  | false =>
    have hg : d55452 p = 1 := by simpa only [d55453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2467 p hg
    simpa only [d55453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2469 (p : Pattern) (guard : d55454 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 46 with
  | false =>
    have hg : d55453 p = 1 := by simpa only [d55454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2468 p hg
    simpa only [d55454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2470 (p : Pattern) (guard : d55455 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 45 with
  | false =>
    have hg : d55454 p = 1 := by simpa only [d55455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d55455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2471 (p : Pattern) (guard : d55456 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 30 with
  | false =>
    have hg : d55455 p = 1 := by simpa only [d55456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2470 p hg
    simpa only [d55456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2472 (p : Pattern) (guard : d55457 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 29 with
  | false =>
    have hg : d55456 p = 1 := by simpa only [d55457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2471 p hg
    simpa only [d55457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2473 (p : Pattern) (guard : d55458 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 28 with
  | false =>
    have hg : d55457 p = 1 := by simpa only [d55458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2472 p hg
    simpa only [d55458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2474 (p : Pattern) (guard : d55459 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 27 with
  | false =>
    have hg : d55458 p = 1 := by simpa only [d55459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2473 p hg
    simpa only [d55459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2475 (p : Pattern) (guard : d55460 p = 1) : d47911 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 25 with
  | false =>
    have hg : d55459 p = 1 := by simpa only [d55460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2474 p hg
    simpa only [d55460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d55460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d55460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2476 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2477 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2478 (p : Pattern) (guard : d65729 p = 1) : d47911 p ≤ (0 : Int) + d47911 p := by
  omega
theorem compare2479 (p : Pattern) (guard : d54976 p = 1) : d47911 p ≤ (0 : Int) + d47911 p := by
  omega
theorem compare2480 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2481 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2482 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2483 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (0 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2484 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (0 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2485 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (0 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2486 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (0 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2487 (p : Pattern) (guard : d25 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare56 p hg
    simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2488 (p : Pattern) (guard : d0 p = 1) : d47662 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2489 (p : Pattern) (guard : d26 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2487 p hg
    simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2490 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2489 p hg
    simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2491 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (0 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2492 (p : Pattern) (guard : d28 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2490 p hg
    simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2493 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2494 (p : Pattern) (guard : d29 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2492 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2495 (p : Pattern) (guard : d30 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2494 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2496 (p : Pattern) (guard : d31 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2495 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2497 (p : Pattern) (guard : d32 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2496 p hg
    simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2498 (p : Pattern) (guard : d33 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2497 p hg
    simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2499 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Soko22Hazard87
