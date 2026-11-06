import NetHack.Soko22Hazard87.Compare148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37250 (p : Pattern) (guard : d317923 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317922 p = 1 := by simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37249 p hg
    simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37251 (p : Pattern) (guard : d317924 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317923 p = 1 := by simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37250 p hg
    simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37252 (p : Pattern) (guard : d317925 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317919 p = 1 := by simpa only [d317925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37246 p hg
    simpa only [d317925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317924 p = 1 := by simpa only [d317925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37251 p hg
    simpa only [d317925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37253 (p : Pattern) (guard : d317926 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317925 p = 1 := by simpa only [d317926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37252 p hg
    simpa only [d317926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37254 (p : Pattern) (guard : d317927 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317926 p = 1 := by simpa only [d317927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37253 p hg
    simpa only [d317927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37255 (p : Pattern) (guard : d317928 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317927 p = 1 := by simpa only [d317928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37254 p hg
    simpa only [d317928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37256 (p : Pattern) (guard : d317929 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317920 p = 1 := by simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37247 p hg
    simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37257 (p : Pattern) (guard : d317930 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317929 p = 1 := by simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37256 p hg
    simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37258 (p : Pattern) (guard : d317931 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317930 p = 1 := by simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37257 p hg
    simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37259 (p : Pattern) (guard : d317932 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317931 p = 1 := by simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37258 p hg
    simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37260 (p : Pattern) (guard : d317933 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317924 p = 1 := by simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37251 p hg
    simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317932 p = 1 := by simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37259 p hg
    simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37261 (p : Pattern) (guard : d317934 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317933 p = 1 := by simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37260 p hg
    simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37262 (p : Pattern) (guard : d317935 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317934 p = 1 := by simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37261 p hg
    simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37263 (p : Pattern) (guard : d317936 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317935 p = 1 := by simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37262 p hg
    simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37264 (p : Pattern) (guard : d317937 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317928 p = 1 := by simpa only [d317937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37255 p hg
    simpa only [d317937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317936 p = 1 := by simpa only [d317937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37263 p hg
    simpa only [d317937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37265 (p : Pattern) (guard : d317938 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317937 p = 1 := by simpa only [d317938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37264 p hg
    simpa only [d317938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37266 (p : Pattern) (guard : d317939 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317924 p = 1 := by simpa only [d317939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37251 p hg
    simpa only [d317939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37267 (p : Pattern) (guard : d317940 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317939 p = 1 := by simpa only [d317940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37266 p hg
    simpa only [d317940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37268 (p : Pattern) (guard : d317941 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317940 p = 1 := by simpa only [d317941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37267 p hg
    simpa only [d317941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37269 (p : Pattern) (guard : d317942 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317941 p = 1 := by simpa only [d317942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37268 p hg
    simpa only [d317942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37270 (p : Pattern) (guard : d317943 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317942 p = 1 := by simpa only [d317943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37269 p hg
    simpa only [d317943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37271 (p : Pattern) (guard : d317944 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317943 p = 1 := by simpa only [d317944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d317944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37272 (p : Pattern) (guard : d317945 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317938 p = 1 := by simpa only [d317945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37265 p hg
    simpa only [d317945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317944 p = 1 := by simpa only [d317945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37271 p hg
    simpa only [d317945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37273 (p : Pattern) (guard : d317946 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317945 p = 1 := by simpa only [d317946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37272 p hg
    simpa only [d317946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37274 (p : Pattern) (guard : d317947 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317946 p = 1 := by simpa only [d317947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37273 p hg
    simpa only [d317947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37275 (p : Pattern) (guard : d317948 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317948, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317948, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317947 p = 1 := by simpa only [d317948, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37274 p hg
    simpa only [d317948, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37276 (p : Pattern) (guard : d317949 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317948 p = 1 := by simpa only [d317949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d317949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37277 (p : Pattern) (guard : d317950 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317932 p = 1 := by simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37259 p hg
    simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37278 (p : Pattern) (guard : d317951 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317950 p = 1 := by simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37277 p hg
    simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37279 (p : Pattern) (guard : d317952 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317951 p = 1 := by simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37278 p hg
    simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37280 (p : Pattern) (guard : d317953 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317952 p = 1 := by simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37279 p hg
    simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37281 (p : Pattern) (guard : d317954 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317953 p = 1 := by simpa only [d317954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37280 p hg
    simpa only [d317954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37282 (p : Pattern) (guard : d317955 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317954 p = 1 := by simpa only [d317955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37281 p hg
    simpa only [d317955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37283 (p : Pattern) (guard : d317956 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317955 p = 1 := by simpa only [d317956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37282 p hg
    simpa only [d317956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37284 (p : Pattern) (guard : d317957 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317956 p = 1 := by simpa only [d317957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37283 p hg
    simpa only [d317957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37285 (p : Pattern) (guard : d317958 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317957 p = 1 := by simpa only [d317958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37284 p hg
    simpa only [d317958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37286 (p : Pattern) (guard : d317959 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317959, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317959, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317958 p = 1 := by simpa only [d317959, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37285 p hg
    simpa only [d317959, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37287 (p : Pattern) (guard : d317960 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317959 p = 1 := by simpa only [d317960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37286 p hg
    simpa only [d317960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37288 (p : Pattern) (guard : d317961 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317949 p = 1 := by simpa only [d317961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37276 p hg
    simpa only [d317961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317960 p = 1 := by simpa only [d317961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37287 p hg
    simpa only [d317961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37289 (p : Pattern) (guard : d317962 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317961 p = 1 := by simpa only [d317962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37288 p hg
    simpa only [d317962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37290 (p : Pattern) (guard : d317963 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d317962 p = 1 := by simpa only [d317963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37289 p hg
    simpa only [d317963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37291 (p : Pattern) (guard : d317964 p = 1) : d50492 p ≤ (3 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d317963 p = 1 := by simpa only [d317964, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37290 p hg
    simpa only [d317964, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317964, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d317964, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37292 (p : Pattern) (guard : d317965 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d317872 p = 1 := by simpa only [d317965, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37087 p hg
    simpa only [d317965, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317964 p = 1 := by simpa only [d317965, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37291 p hg
    simpa only [d317965, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37293 (p : Pattern) (guard : d317966 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317965 p = 1 := by simpa only [d317966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37292 p hg
    simpa only [d317966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37294 (p : Pattern) (guard : d317967 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317966 p = 1 := by simpa only [d317967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37293 p hg
    simpa only [d317967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37295 (p : Pattern) (guard : d317968 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317967 p = 1 := by simpa only [d317968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37294 p hg
    simpa only [d317968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37296 (p : Pattern) (guard : d317969 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317968 p = 1 := by simpa only [d317969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37295 p hg
    simpa only [d317969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37297 (p : Pattern) (guard : d317970 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317969 p = 1 := by simpa only [d317970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37296 p hg
    simpa only [d317970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37298 (p : Pattern) (guard : d317971 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317970 p = 1 := by simpa only [d317971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37297 p hg
    simpa only [d317971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37299 (p : Pattern) (guard : d317972 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317971 p = 1 := by simpa only [d317972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37298 p hg
    simpa only [d317972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37300 (p : Pattern) (guard : d317973 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317972 p = 1 := by simpa only [d317973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37299 p hg
    simpa only [d317973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37301 (p : Pattern) (guard : d317974 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317973 p = 1 := by simpa only [d317974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37300 p hg
    simpa only [d317974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37302 (p : Pattern) (guard : d317975 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d317690 p = 1 := by simpa only [d317975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36668 p hg
    simpa only [d317975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317974 p = 1 := by simpa only [d317975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37301 p hg
    simpa only [d317975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37303 (p : Pattern) (guard : d2013 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare37304 (p : Pattern) (guard : d2027 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37303 p hg
    simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37305 (p : Pattern) (guard : d2028 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37304 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37306 (p : Pattern) (guard : d2029 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37305 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37307 (p : Pattern) (guard : d2030 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37306 p hg
    simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37308 (p : Pattern) (guard : d2031 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37307 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37309 (p : Pattern) (guard : d317063 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37308 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37310 (p : Pattern) (guard : d317064 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37309 p hg
    simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37311 (p : Pattern) (guard : d317065 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37310 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37312 (p : Pattern) (guard : d317066 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37311 p hg
    simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37313 (p : Pattern) (guard : d317067 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317066 p = 1 := by simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37312 p hg
    simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37314 (p : Pattern) (guard : d317068 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317067 p = 1 := by simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37313 p hg
    simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37315 (p : Pattern) (guard : d317069 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317068 p = 1 := by simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37314 p hg
    simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37316 (p : Pattern) (guard : d317070 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37310 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37317 (p : Pattern) (guard : d317071 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37316 p hg
    simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37318 (p : Pattern) (guard : d317072 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317071 p = 1 := by simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37317 p hg
    simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37319 (p : Pattern) (guard : d317073 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317072 p = 1 := by simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37318 p hg
    simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37320 (p : Pattern) (guard : d317074 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317073 p = 1 := by simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37319 p hg
    simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37321 (p : Pattern) (guard : d317075 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317069 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37315 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317074 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37320 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37322 (p : Pattern) (guard : d317076 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317075 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37321 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37323 (p : Pattern) (guard : d27032 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37307 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37324 (p : Pattern) (guard : d235783 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37323 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37325 (p : Pattern) (guard : d235784 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37324 p hg
    simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37326 (p : Pattern) (guard : d317976 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37310 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37325 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37327 (p : Pattern) (guard : d317977 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37326 p hg
    simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37328 (p : Pattern) (guard : d317978 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317977 p = 1 := by simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37327 p hg
    simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37329 (p : Pattern) (guard : d317979 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317978 p = 1 := by simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37328 p hg
    simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37330 (p : Pattern) (guard : d317980 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317979 p = 1 := by simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37329 p hg
    simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37331 (p : Pattern) (guard : d317094 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37325 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37332 (p : Pattern) (guard : d317095 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37331 p hg
    simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37333 (p : Pattern) (guard : d317096 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317095 p = 1 := by simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37332 p hg
    simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37334 (p : Pattern) (guard : d317097 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317096 p = 1 := by simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37333 p hg
    simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37335 (p : Pattern) (guard : d317098 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317097 p = 1 := by simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37334 p hg
    simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37336 (p : Pattern) (guard : d317981 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317980 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37330 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317098 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37335 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37337 (p : Pattern) (guard : d317982 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317981 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37336 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37338 (p : Pattern) (guard : d317983 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317076 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37322 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317982 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37337 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37339 (p : Pattern) (guard : d317984 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317983 p = 1 := by simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37338 p hg
    simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37340 (p : Pattern) (guard : d317985 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317984 p = 1 := by simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37339 p hg
    simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37341 (p : Pattern) (guard : d317099 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317098 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37335 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37342 (p : Pattern) (guard : d317100 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317099 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37341 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37343 (p : Pattern) (guard : d317986 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317982 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37337 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317100 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37342 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37344 (p : Pattern) (guard : d317987 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317986 p = 1 := by simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37343 p hg
    simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37345 (p : Pattern) (guard : d317988 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317987 p = 1 := by simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37344 p hg
    simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37346 (p : Pattern) (guard : d317989 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317985 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37340 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317988 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37345 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37347 (p : Pattern) (guard : d317990 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317988 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37345 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37348 (p : Pattern) (guard : d317991 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317989 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37346 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317990 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37347 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37349 (p : Pattern) (guard : d317992 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317991 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37348 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37350 (p : Pattern) (guard : d317993 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317992 p = 1 := by simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37349 p hg
    simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37351 (p : Pattern) (guard : d317994 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317993 p = 1 := by simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37350 p hg
    simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37352 (p : Pattern) (guard : d317995 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317990 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37347 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37353 (p : Pattern) (guard : d317996 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317995 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37352 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37354 (p : Pattern) (guard : d317997 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317996 p = 1 := by simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37353 p hg
    simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37355 (p : Pattern) (guard : d317998 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317997 p = 1 := by simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37354 p hg
    simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37356 (p : Pattern) (guard : d317999 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37351 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317998 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37355 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37357 (p : Pattern) (guard : d318000 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317999 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37356 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37358 (p : Pattern) (guard : d318001 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318000 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37357 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37359 (p : Pattern) (guard : d318002 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318001 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37358 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37360 (p : Pattern) (guard : d318003 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317998 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37355 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37361 (p : Pattern) (guard : d318004 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318003 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37360 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37362 (p : Pattern) (guard : d318005 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318004 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37361 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37363 (p : Pattern) (guard : d318006 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318005 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37362 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37364 (p : Pattern) (guard : d318007 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318002 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37359 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318006 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37363 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37365 (p : Pattern) (guard : d318008 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318007 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37364 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37366 (p : Pattern) (guard : d318009 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318008 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37365 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37367 (p : Pattern) (guard : d318010 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318009 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37366 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37368 (p : Pattern) (guard : d318011 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318010 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37367 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37369 (p : Pattern) (guard : d318012 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318011 p = 1 := by simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37368 p hg
    simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37370 (p : Pattern) (guard : d318013 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d318013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318012 p = 1 := by simpa only [d318013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37369 p hg
    simpa only [d318013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37371 (p : Pattern) (guard : d318014 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318013 p = 1 := by simpa only [d318014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37370 p hg
    simpa only [d318014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d318014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37372 (p : Pattern) (guard : d317985 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317984 p = 1 := by simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37339 p hg
    simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37373 (p : Pattern) (guard : d317988 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317987 p = 1 := by simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37344 p hg
    simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37374 (p : Pattern) (guard : d317989 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317985 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37372 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317988 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37373 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37375 (p : Pattern) (guard : d317990 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317988 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37373 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37376 (p : Pattern) (guard : d317991 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317989 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37374 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317990 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37375 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37377 (p : Pattern) (guard : d317992 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317991 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37376 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37378 (p : Pattern) (guard : d317993 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317992 p = 1 := by simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37377 p hg
    simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37379 (p : Pattern) (guard : d317994 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317993 p = 1 := by simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37378 p hg
    simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37380 (p : Pattern) (guard : d317995 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317990 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37375 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37381 (p : Pattern) (guard : d317996 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317995 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37380 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37382 (p : Pattern) (guard : d317997 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317996 p = 1 := by simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37381 p hg
    simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37383 (p : Pattern) (guard : d317998 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317997 p = 1 := by simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37382 p hg
    simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37384 (p : Pattern) (guard : d317999 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37379 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317998 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37383 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37385 (p : Pattern) (guard : d318000 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317999 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37384 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37386 (p : Pattern) (guard : d318001 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318000 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37385 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37387 (p : Pattern) (guard : d318002 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318001 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37386 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37388 (p : Pattern) (guard : d318003 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317998 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37383 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37389 (p : Pattern) (guard : d318004 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318003 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37388 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37390 (p : Pattern) (guard : d318005 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318004 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37389 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37391 (p : Pattern) (guard : d318006 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318005 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37390 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37392 (p : Pattern) (guard : d318007 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318002 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37387 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318006 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37391 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37393 (p : Pattern) (guard : d318008 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318007 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37392 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37394 (p : Pattern) (guard : d318009 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318008 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37393 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37395 (p : Pattern) (guard : d318010 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318009 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37394 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37396 (p : Pattern) (guard : d318011 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318010 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37395 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37397 (p : Pattern) (guard : d318015 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318001 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37358 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37398 (p : Pattern) (guard : d318016 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318005 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37362 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37399 (p : Pattern) (guard : d318017 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318015 p = 1 := by simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318016 p = 1 := by simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37398 p hg
    simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37400 (p : Pattern) (guard : d318018 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318017 p = 1 := by simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37399 p hg
    simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37401 (p : Pattern) (guard : d318019 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318018 p = 1 := by simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37400 p hg
    simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37402 (p : Pattern) (guard : d318020 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318019 p = 1 := by simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37401 p hg
    simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37403 (p : Pattern) (guard : d318021 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318020 p = 1 := by simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37402 p hg
    simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37404 (p : Pattern) (guard : d318022 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d318011 p = 1 := by simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37396 p hg
    simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318021 p = 1 := by simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37403 p hg
    simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37405 (p : Pattern) (guard : d318023 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d318012 p = 1 := by simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37369 p hg
    simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318022 p = 1 := by simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37404 p hg
    simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37406 (p : Pattern) (guard : d318024 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318023 p = 1 := by simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37405 p hg
    simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37407 (p : Pattern) (guard : d318025 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318014 p = 1 := by simpa only [d318025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37371 p hg
    simpa only [d318025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318024 p = 1 := by simpa only [d318025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37406 p hg
    simpa only [d318025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37408 (p : Pattern) (guard : d318026 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318000 p = 1 := by simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37357 p hg
    simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37409 (p : Pattern) (guard : d318027 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318026 p = 1 := by simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37408 p hg
    simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37410 (p : Pattern) (guard : d318028 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318004 p = 1 := by simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37361 p hg
    simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37411 (p : Pattern) (guard : d318029 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318028 p = 1 := by simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37410 p hg
    simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37412 (p : Pattern) (guard : d318030 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318027 p = 1 := by simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37409 p hg
    simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318029 p = 1 := by simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37411 p hg
    simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37413 (p : Pattern) (guard : d318031 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318030 p = 1 := by simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37412 p hg
    simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37414 (p : Pattern) (guard : d318032 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318031 p = 1 := by simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37413 p hg
    simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37415 (p : Pattern) (guard : d318033 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318032 p = 1 := by simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37414 p hg
    simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37416 (p : Pattern) (guard : d318034 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317999 p = 1 := by simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37356 p hg
    simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37417 (p : Pattern) (guard : d318035 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318034 p = 1 := by simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37416 p hg
    simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37418 (p : Pattern) (guard : d318036 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318035 p = 1 := by simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37417 p hg
    simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37419 (p : Pattern) (guard : d318037 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318003 p = 1 := by simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37360 p hg
    simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37420 (p : Pattern) (guard : d318038 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318037 p = 1 := by simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37419 p hg
    simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37421 (p : Pattern) (guard : d318039 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318038 p = 1 := by simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37420 p hg
    simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37422 (p : Pattern) (guard : d318040 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318036 p = 1 := by simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37418 p hg
    simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318039 p = 1 := by simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37421 p hg
    simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37423 (p : Pattern) (guard : d318041 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318040 p = 1 := by simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37422 p hg
    simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37424 (p : Pattern) (guard : d318042 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318041 p = 1 := by simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37423 p hg
    simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37425 (p : Pattern) (guard : d317163 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317076 p = 1 := by simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37322 p hg
    simpa only [d317163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37426 (p : Pattern) (guard : d317164 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317164, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317164, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317163 p = 1 := by simpa only [d317164, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37425 p hg
    simpa only [d317164, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37427 (p : Pattern) (guard : d317165 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317165, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317165, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317164 p = 1 := by simpa only [d317165, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37426 p hg
    simpa only [d317165, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37428 (p : Pattern) (guard : d317166 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317076 p = 1 := by simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37322 p hg
    simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37429 (p : Pattern) (guard : d317167 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317167, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317167, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317166 p = 1 := by simpa only [d317167, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37428 p hg
    simpa only [d317167, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37430 (p : Pattern) (guard : d317168 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317168, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317168, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317167 p = 1 := by simpa only [d317168, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37429 p hg
    simpa only [d317168, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37431 (p : Pattern) (guard : d317169 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317165 p = 1 := by simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37427 p hg
    simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317168 p = 1 := by simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37430 p hg
    simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37432 (p : Pattern) (guard : d318043 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317169 p = 1 := by simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37431 p hg
    simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317989 p = 1 := by simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37346 p hg
    simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37433 (p : Pattern) (guard : d318044 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318043 p = 1 := by simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37432 p hg
    simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37434 (p : Pattern) (guard : d318045 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318044 p = 1 := by simpa only [d318045, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37433 p hg
    simpa only [d318045, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318045, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d318045, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37435 (p : Pattern) (guard : d318046 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318046, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d318046, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318045 p = 1 := by simpa only [d318046, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37434 p hg
    simpa only [d318046, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37436 (p : Pattern) (guard : d318047 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318046 p = 1 := by simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37435 p hg
    simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317994 p = 1 := by simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37351 p hg
    simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37437 (p : Pattern) (guard : d318048 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318047 p = 1 := by simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37436 p hg
    simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37438 (p : Pattern) (guard : d318049 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318048 p = 1 := by simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37437 p hg
    simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37439 (p : Pattern) (guard : d318050 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318049 p = 1 := by simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37438 p hg
    simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37440 (p : Pattern) (guard : d318051 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318050 p = 1 := by simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37439 p hg
    simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318002 p = 1 := by simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37359 p hg
    simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37441 (p : Pattern) (guard : d318052 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318051 p = 1 := by simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37440 p hg
    simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37442 (p : Pattern) (guard : d318053 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37351 p hg
    simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37443 (p : Pattern) (guard : d318054 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318053 p = 1 := by simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37442 p hg
    simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37444 (p : Pattern) (guard : d318055 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318054 p = 1 := by simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37443 p hg
    simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37445 (p : Pattern) (guard : d318056 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318055 p = 1 := by simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37444 p hg
    simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37446 (p : Pattern) (guard : d318057 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318056 p = 1 := by simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37445 p hg
    simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37447 (p : Pattern) (guard : d318058 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318057 p = 1 := by simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37446 p hg
    simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37448 (p : Pattern) (guard : d318059 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318052 p = 1 := by simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37441 p hg
    simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318058 p = 1 := by simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37447 p hg
    simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37449 (p : Pattern) (guard : d318060 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d318042 p = 1 := by simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37424 p hg
    simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318059 p = 1 := by simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37448 p hg
    simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37450 (p : Pattern) (guard : d318061 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d318033 p = 1 := by simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37415 p hg
    simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318060 p = 1 := by simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37449 p hg
    simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37451 (p : Pattern) (guard : d318062 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318062, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318062, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318061 p = 1 := by simpa only [d318062, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37450 p hg
    simpa only [d318062, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37452 (p : Pattern) (guard : d318026 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318000 p = 1 := by simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37385 p hg
    simpa only [d318026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37453 (p : Pattern) (guard : d318027 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318026 p = 1 := by simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37452 p hg
    simpa only [d318027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37454 (p : Pattern) (guard : d318028 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318004 p = 1 := by simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37389 p hg
    simpa only [d318028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37455 (p : Pattern) (guard : d318029 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318028 p = 1 := by simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37454 p hg
    simpa only [d318029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37456 (p : Pattern) (guard : d318030 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318027 p = 1 := by simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37453 p hg
    simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318029 p = 1 := by simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37455 p hg
    simpa only [d318030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37457 (p : Pattern) (guard : d318031 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318030 p = 1 := by simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37456 p hg
    simpa only [d318031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37458 (p : Pattern) (guard : d318032 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318031 p = 1 := by simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37457 p hg
    simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37459 (p : Pattern) (guard : d318033 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318032 p = 1 := by simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37458 p hg
    simpa only [d318033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37460 (p : Pattern) (guard : d318034 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317999 p = 1 := by simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37384 p hg
    simpa only [d318034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37461 (p : Pattern) (guard : d318035 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318034 p = 1 := by simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37460 p hg
    simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37462 (p : Pattern) (guard : d318036 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318035 p = 1 := by simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37461 p hg
    simpa only [d318036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37463 (p : Pattern) (guard : d318037 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318003 p = 1 := by simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37388 p hg
    simpa only [d318037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37464 (p : Pattern) (guard : d318038 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318037 p = 1 := by simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37463 p hg
    simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37465 (p : Pattern) (guard : d318039 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318038 p = 1 := by simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37464 p hg
    simpa only [d318039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37466 (p : Pattern) (guard : d318040 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318036 p = 1 := by simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37462 p hg
    simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318039 p = 1 := by simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37465 p hg
    simpa only [d318040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37467 (p : Pattern) (guard : d318041 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318040 p = 1 := by simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37466 p hg
    simpa only [d318041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37468 (p : Pattern) (guard : d318042 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318041 p = 1 := by simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37467 p hg
    simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37469 (p : Pattern) (guard : d317165 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317165, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317165, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317164 p = 1 := by simpa only [d317165, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37426 p hg
    simpa only [d317165, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37470 (p : Pattern) (guard : d317168 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317168, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317168, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317167 p = 1 := by simpa only [d317168, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37429 p hg
    simpa only [d317168, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37471 (p : Pattern) (guard : d317169 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317165 p = 1 := by simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37469 p hg
    simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317168 p = 1 := by simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37470 p hg
    simpa only [d317169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37472 (p : Pattern) (guard : d318043 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317169 p = 1 := by simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37471 p hg
    simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317989 p = 1 := by simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37374 p hg
    simpa only [d318043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37473 (p : Pattern) (guard : d318044 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318043 p = 1 := by simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37472 p hg
    simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d318044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37474 (p : Pattern) (guard : d318045 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318044 p = 1 := by simpa only [d318045, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37473 p hg
    simpa only [d318045, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318045, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d318045, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37475 (p : Pattern) (guard : d318046 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318046, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d318046, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318045 p = 1 := by simpa only [d318046, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37474 p hg
    simpa only [d318046, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37476 (p : Pattern) (guard : d318047 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318046 p = 1 := by simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37475 p hg
    simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317994 p = 1 := by simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37379 p hg
    simpa only [d318047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37477 (p : Pattern) (guard : d318048 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318047 p = 1 := by simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37476 p hg
    simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37478 (p : Pattern) (guard : d318049 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318048 p = 1 := by simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37477 p hg
    simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37479 (p : Pattern) (guard : d318050 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318049 p = 1 := by simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37478 p hg
    simpa only [d318050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37480 (p : Pattern) (guard : d318051 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318050 p = 1 := by simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37479 p hg
    simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318002 p = 1 := by simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37387 p hg
    simpa only [d318051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37481 (p : Pattern) (guard : d318052 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318051 p = 1 := by simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37480 p hg
    simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37482 (p : Pattern) (guard : d318053 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37379 p hg
    simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37483 (p : Pattern) (guard : d318054 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318053 p = 1 := by simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37482 p hg
    simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37484 (p : Pattern) (guard : d318055 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318054 p = 1 := by simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37483 p hg
    simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37485 (p : Pattern) (guard : d318056 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318055 p = 1 := by simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37484 p hg
    simpa only [d318056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37486 (p : Pattern) (guard : d318057 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318056 p = 1 := by simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37485 p hg
    simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37487 (p : Pattern) (guard : d318058 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d318057 p = 1 := by simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37486 p hg
    simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d318058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37488 (p : Pattern) (guard : d318059 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318052 p = 1 := by simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37481 p hg
    simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318058 p = 1 := by simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37487 p hg
    simpa only [d318059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37489 (p : Pattern) (guard : d318060 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d318042 p = 1 := by simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37468 p hg
    simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318059 p = 1 := by simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37488 p hg
    simpa only [d318060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37490 (p : Pattern) (guard : d318061 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d318033 p = 1 := by simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37459 p hg
    simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318060 p = 1 := by simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37489 p hg
    simpa only [d318061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37491 (p : Pattern) (guard : d318063 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318026 p = 1 := by simpa only [d318063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37408 p hg
    simpa only [d318063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37492 (p : Pattern) (guard : d318064 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318028 p = 1 := by simpa only [d318064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37410 p hg
    simpa only [d318064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37493 (p : Pattern) (guard : d318065 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318063 p = 1 := by simpa only [d318065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37491 p hg
    simpa only [d318065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318064 p = 1 := by simpa only [d318065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37492 p hg
    simpa only [d318065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37494 (p : Pattern) (guard : d318066 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318065 p = 1 := by simpa only [d318066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37493 p hg
    simpa only [d318066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37495 (p : Pattern) (guard : d318067 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318066 p = 1 := by simpa only [d318067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37494 p hg
    simpa only [d318067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37496 (p : Pattern) (guard : d318068 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318067 p = 1 := by simpa only [d318068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37495 p hg
    simpa only [d318068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37497 (p : Pattern) (guard : d318069 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318035 p = 1 := by simpa only [d318069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37417 p hg
    simpa only [d318069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37498 (p : Pattern) (guard : d318070 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318038 p = 1 := by simpa only [d318070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37420 p hg
    simpa only [d318070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d318070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37499 (p : Pattern) (guard : d318071 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318069 p = 1 := by simpa only [d318071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37497 p hg
    simpa only [d318071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318070 p = 1 := by simpa only [d318071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37498 p hg
    simpa only [d318071, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
