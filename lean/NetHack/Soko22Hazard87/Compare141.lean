import NetHack.Soko22Hazard87.Compare140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35250 (p : Pattern) (guard : d285918 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285917 p = 1 := by simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35249 p hg
    simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d285918, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35251 (p : Pattern) (guard : d285919 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285918 p = 1 := by simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35250 p hg
    simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257233 p = 1 := by simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35039 p hg
    simpa only [d285919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35252 (p : Pattern) (guard : d285920 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285919 p = 1 := by simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35251 p hg
    simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257234 p = 1 := by simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35041 p hg
    simpa only [d285920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35253 (p : Pattern) (guard : d285921 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d285920 p = 1 := by simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257235 p = 1 := by simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35042 p hg
    simpa only [d285921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35254 (p : Pattern) (guard : d285922 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285921 p = 1 := by simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35253 p hg
    simpa only [d285922, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35255 (p : Pattern) (guard : d285923 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285922 p = 1 := by simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35254 p hg
    simpa only [d285923, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35256 (p : Pattern) (guard : d285924 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285923 p = 1 := by simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35255 p hg
    simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257238 p = 1 := by simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35045 p hg
    simpa only [d285924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35257 (p : Pattern) (guard : d285925 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285924 p = 1 := by simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35256 p hg
    simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257239 p = 1 := by simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35047 p hg
    simpa only [d285925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35258 (p : Pattern) (guard : d285926 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285925 p = 1 := by simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35257 p hg
    simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d285926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35259 (p : Pattern) (guard : d285927 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285926 p = 1 := by simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35258 p hg
    simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d285927, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35260 (p : Pattern) (guard : d285928 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285927 p = 1 := by simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35259 p hg
    simpa only [d285928, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35261 (p : Pattern) (guard : d285929 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285928 p = 1 := by simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35260 p hg
    simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257243 p = 1 := by simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35052 p hg
    simpa only [d285929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35262 (p : Pattern) (guard : d285930 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285929 p = 1 := by simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d285930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35263 (p : Pattern) (guard : d285931 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285930 p = 1 := by simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35262 p hg
    simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d285931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35264 (p : Pattern) (guard : d285932 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285931 p = 1 := by simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35263 p hg
    simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d285932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35265 (p : Pattern) (guard : d285933 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285932 p = 1 := by simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35264 p hg
    simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257247 p = 1 := by simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35056 p hg
    simpa only [d285933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35266 (p : Pattern) (guard : d285934 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d285933 p = 1 := by simpa only [d285934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35265 p hg
    simpa only [d285934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d285934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35267 (p : Pattern) (guard : d285935 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285934 p = 1 := by simpa only [d285935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35266 p hg
    simpa only [d285935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257249 p = 1 := by simpa only [d285935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35058 p hg
    simpa only [d285935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35268 (p : Pattern) (guard : d285936 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d285936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285935 p = 1 := by simpa only [d285936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35267 p hg
    simpa only [d285936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35269 (p : Pattern) (guard : d285937 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d285937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285936 p = 1 := by simpa only [d285937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35268 p hg
    simpa only [d285937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35270 (p : Pattern) (guard : d285938 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285938, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285938, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285937 p = 1 := by simpa only [d285938, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35269 p hg
    simpa only [d285938, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35271 (p : Pattern) (guard : d285939 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d285939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285938 p = 1 := by simpa only [d285939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35270 p hg
    simpa only [d285939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35272 (p : Pattern) (guard : d285940 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285939 p = 1 := by simpa only [d285940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35271 p hg
    simpa only [d285940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d285940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35273 (p : Pattern) (guard : d285941 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d285940 p = 1 := by simpa only [d285941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35272 p hg
    simpa only [d285941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d285941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35274 (p : Pattern) (guard : d285942 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d285941 p = 1 := by simpa only [d285942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35273 p hg
    simpa only [d285942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d285942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35275 (p : Pattern) (guard : d285943 p = 1) : d50492 p ≤ (3 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d285942 p = 1 := by simpa only [d285943, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35274 p hg
    simpa only [d285943, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285943, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d285943, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35276 (p : Pattern) (guard : d285944 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d285914 p = 1 := by simpa only [d285944, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35225 p hg
    simpa only [d285944, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285943 p = 1 := by simpa only [d285944, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35275 p hg
    simpa only [d285944, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35277 (p : Pattern) (guard : d285945 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d285945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285944 p = 1 := by simpa only [d285945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35276 p hg
    simpa only [d285945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35278 (p : Pattern) (guard : d285946 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d285946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285945 p = 1 := by simpa only [d285946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35277 p hg
    simpa only [d285946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35279 (p : Pattern) (guard : d285947 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d285947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285946 p = 1 := by simpa only [d285947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35278 p hg
    simpa only [d285947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35280 (p : Pattern) (guard : d285948 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d285948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285947 p = 1 := by simpa only [d285948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35279 p hg
    simpa only [d285948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35281 (p : Pattern) (guard : d285949 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d285949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285948 p = 1 := by simpa only [d285949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35280 p hg
    simpa only [d285949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35282 (p : Pattern) (guard : d285950 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d257264 p = 1 := by simpa only [d285950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35074 p hg
    simpa only [d285950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285949 p = 1 := by simpa only [d285950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35281 p hg
    simpa only [d285950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35283 (p : Pattern) (guard : d285951 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285890 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35284 (p : Pattern) (guard : d285952 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285951 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35283 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35285 (p : Pattern) (guard : d285953 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285952 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35284 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35286 (p : Pattern) (guard : d285954 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285953 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35285 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35287 (p : Pattern) (guard : d285955 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285954 p = 1 := by simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35286 p hg
    simpa only [d285955, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35288 (p : Pattern) (guard : d285956 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d285956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285955 p = 1 := by simpa only [d285956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35287 p hg
    simpa only [d285956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35289 (p : Pattern) (guard : d285957 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285956 p = 1 := by simpa only [d285957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35288 p hg
    simpa only [d285957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d285957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35290 (p : Pattern) (guard : d285951 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285890 p = 1 := by simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35161 p hg
    simpa only [d285951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35291 (p : Pattern) (guard : d285952 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285951 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35290 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35292 (p : Pattern) (guard : d285953 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285952 p = 1 := by simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35291 p hg
    simpa only [d285953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35293 (p : Pattern) (guard : d285954 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285953 p = 1 := by simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35292 p hg
    simpa only [d285954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35294 (p : Pattern) (guard : d285958 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285897 p = 1 := by simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35176 p hg
    simpa only [d285958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35295 (p : Pattern) (guard : d285959 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285958 p = 1 := by simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35294 p hg
    simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35296 (p : Pattern) (guard : d285960 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285959 p = 1 := by simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35295 p hg
    simpa only [d285960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35297 (p : Pattern) (guard : d285961 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285960 p = 1 := by simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35296 p hg
    simpa only [d285961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35298 (p : Pattern) (guard : d285962 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d285954 p = 1 := by simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35293 p hg
    simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285961 p = 1 := by simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35297 p hg
    simpa only [d285962, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35299 (p : Pattern) (guard : d285963 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d285955 p = 1 := by simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35287 p hg
    simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285962 p = 1 := by simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35298 p hg
    simpa only [d285963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35300 (p : Pattern) (guard : d285964 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285963 p = 1 := by simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35299 p hg
    simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d285964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35301 (p : Pattern) (guard : d285965 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d285957 p = 1 := by simpa only [d285965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35289 p hg
    simpa only [d285965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285964 p = 1 := by simpa only [d285965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35300 p hg
    simpa only [d285965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35302 (p : Pattern) (guard : d285966 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285887 p = 1 := by simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35303 (p : Pattern) (guard : d285967 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285966 p = 1 := by simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35302 p hg
    simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35304 (p : Pattern) (guard : d285968 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285967 p = 1 := by simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35303 p hg
    simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257281 p = 1 := by simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35095 p hg
    simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35305 (p : Pattern) (guard : d285969 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285968 p = 1 := by simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35304 p hg
    simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35306 (p : Pattern) (guard : d285970 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285969 p = 1 := by simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35305 p hg
    simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35307 (p : Pattern) (guard : d285971 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285970 p = 1 := by simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35306 p hg
    simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35308 (p : Pattern) (guard : d285972 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285886 p = 1 := by simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35129 p hg
    simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35309 (p : Pattern) (guard : d285973 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285972 p = 1 := by simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35308 p hg
    simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35310 (p : Pattern) (guard : d285974 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285973 p = 1 := by simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35309 p hg
    simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35311 (p : Pattern) (guard : d285975 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285974 p = 1 := by simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35310 p hg
    simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257288 p = 1 := by simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35102 p hg
    simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35312 (p : Pattern) (guard : d285976 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285975 p = 1 := by simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35311 p hg
    simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35313 (p : Pattern) (guard : d285977 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285976 p = 1 := by simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35312 p hg
    simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35314 (p : Pattern) (guard : d1520 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare35315 (p : Pattern) (guard : d33554 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35314 p hg
    simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d33554, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35316 (p : Pattern) (guard : d286611 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35315 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35317 (p : Pattern) (guard : d286612 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35316 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35318 (p : Pattern) (guard : d286613 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35317 p hg
    simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d286613, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35319 (p : Pattern) (guard : d316227 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35318 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35110 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35320 (p : Pattern) (guard : d534 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare35321 (p : Pattern) (guard : d33559 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d33559, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35322 (p : Pattern) (guard : d316228 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35321 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35323 (p : Pattern) (guard : d316229 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35324 (p : Pattern) (guard : d316230 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35323 p hg
    simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d316230, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35325 (p : Pattern) (guard : d316231 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35324 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34875 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35326 (p : Pattern) (guard : d316232 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35319 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35325 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35327 (p : Pattern) (guard : d316233 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35326 p hg
    simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d316233, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35328 (p : Pattern) (guard : d316234 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35327 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35113 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35329 (p : Pattern) (guard : d316235 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35328 p hg
    simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316235, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35330 (p : Pattern) (guard : d316236 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316235 p = 1 := by simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35329 p hg
    simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316236, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35331 (p : Pattern) (guard : d316237 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316236 p = 1 := by simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35330 p hg
    simpa only [d316237, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35332 (p : Pattern) (guard : d316238 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316237 p = 1 := by simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35331 p hg
    simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316238, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35333 (p : Pattern) (guard : d316239 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316238 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35332 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285875 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35118 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35334 (p : Pattern) (guard : d285991 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35111 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35335 (p : Pattern) (guard : d285992 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35334 p hg
    simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d285992, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35336 (p : Pattern) (guard : d285993 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35335 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34880 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35337 (p : Pattern) (guard : d285994 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35336 p hg
    simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d285994, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35338 (p : Pattern) (guard : d285995 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285994 p = 1 := by simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35337 p hg
    simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d285995, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35339 (p : Pattern) (guard : d285996 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285995 p = 1 := by simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35338 p hg
    simpa only [d285996, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35340 (p : Pattern) (guard : d285997 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285996 p = 1 := by simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35339 p hg
    simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d285997, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35341 (p : Pattern) (guard : d285998 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285997 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35340 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34889 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35342 (p : Pattern) (guard : d316240 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316239 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35333 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285998 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35341 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35343 (p : Pattern) (guard : d316241 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316240 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35342 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285877 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35120 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35344 (p : Pattern) (guard : d316242 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316241 p = 1 := by simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35343 p hg
    simpa only [d316242, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35345 (p : Pattern) (guard : d316243 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316242 p = 1 := by simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35344 p hg
    simpa only [d316243, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35346 (p : Pattern) (guard : d316244 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316243 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35345 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285880 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35123 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35347 (p : Pattern) (guard : d316245 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35346 p hg
    simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285881 p = 1 := by simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35124 p hg
    simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35348 (p : Pattern) (guard : d316246 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316245 p = 1 := by simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35347 p hg
    simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35349 (p : Pattern) (guard : d316247 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316246 p = 1 := by simpa only [d316247, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35348 p hg
    simpa only [d316247, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316247, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d316247, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35350 (p : Pattern) (guard : d316248 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316248, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d316248, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316247 p = 1 := by simpa only [d316248, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35349 p hg
    simpa only [d316248, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35351 (p : Pattern) (guard : d316249 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316248 p = 1 := by simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35350 p hg
    simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285885 p = 1 := by simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35128 p hg
    simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35352 (p : Pattern) (guard : d316250 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316249 p = 1 := by simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35351 p hg
    simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35353 (p : Pattern) (guard : d316251 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316250 p = 1 := by simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35352 p hg
    simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35354 (p : Pattern) (guard : d316252 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316251 p = 1 := by simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35353 p hg
    simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35355 (p : Pattern) (guard : d316253 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316252 p = 1 := by simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35354 p hg
    simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285889 p = 1 := by simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35132 p hg
    simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35356 (p : Pattern) (guard : d316254 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316253 p = 1 := by simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35355 p hg
    simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35357 (p : Pattern) (guard : d286014 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35128 p hg
    simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35358 (p : Pattern) (guard : d286015 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286014 p = 1 := by simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35357 p hg
    simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35359 (p : Pattern) (guard : d286016 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286015 p = 1 := by simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35358 p hg
    simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35360 (p : Pattern) (guard : d286017 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286016 p = 1 := by simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35359 p hg
    simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35361 (p : Pattern) (guard : d286018 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286017 p = 1 := by simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35362 (p : Pattern) (guard : d286019 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d286018 p = 1 := by simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35361 p hg
    simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35363 (p : Pattern) (guard : d316255 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316254 p = 1 := by simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35356 p hg
    simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286019 p = 1 := by simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35362 p hg
    simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35364 (p : Pattern) (guard : d316256 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d285977 p = 1 := by simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35313 p hg
    simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316255 p = 1 := by simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35363 p hg
    simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35365 (p : Pattern) (guard : d316257 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d285971 p = 1 := by simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35307 p hg
    simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316256 p = 1 := by simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35364 p hg
    simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35366 (p : Pattern) (guard : d316258 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316258, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316258, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316257 p = 1 := by simpa only [d316258, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35365 p hg
    simpa only [d316258, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35367 (p : Pattern) (guard : d285966 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285887 p = 1 := by simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35158 p hg
    simpa only [d285966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35368 (p : Pattern) (guard : d285967 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285966 p = 1 := by simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35367 p hg
    simpa only [d285967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35369 (p : Pattern) (guard : d285968 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285967 p = 1 := by simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35368 p hg
    simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257281 p = 1 := by simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35140 p hg
    simpa only [d285968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35370 (p : Pattern) (guard : d285969 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285968 p = 1 := by simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35369 p hg
    simpa only [d285969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35371 (p : Pattern) (guard : d285970 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285969 p = 1 := by simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35370 p hg
    simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35372 (p : Pattern) (guard : d285971 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285970 p = 1 := by simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35371 p hg
    simpa only [d285971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35373 (p : Pattern) (guard : d285972 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285886 p = 1 := by simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35157 p hg
    simpa only [d285972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35374 (p : Pattern) (guard : d285973 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285972 p = 1 := by simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35373 p hg
    simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35375 (p : Pattern) (guard : d285974 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285973 p = 1 := by simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35374 p hg
    simpa only [d285974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35376 (p : Pattern) (guard : d285975 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285974 p = 1 := by simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35375 p hg
    simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257288 p = 1 := by simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35147 p hg
    simpa only [d285975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35377 (p : Pattern) (guard : d285976 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285975 p = 1 := by simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35376 p hg
    simpa only [d285976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35378 (p : Pattern) (guard : d285977 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285976 p = 1 := by simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35377 p hg
    simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35379 (p : Pattern) (guard : d316243 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316242 p = 1 := by simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35344 p hg
    simpa only [d316243, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35380 (p : Pattern) (guard : d316244 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316243 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35379 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285880 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35151 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35381 (p : Pattern) (guard : d316245 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35380 p hg
    simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285881 p = 1 := by simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35152 p hg
    simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35382 (p : Pattern) (guard : d316246 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316245 p = 1 := by simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35381 p hg
    simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35383 (p : Pattern) (guard : d316247 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316246 p = 1 := by simpa only [d316247, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35382 p hg
    simpa only [d316247, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316247, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d316247, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35384 (p : Pattern) (guard : d316248 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316248, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d316248, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316247 p = 1 := by simpa only [d316248, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35383 p hg
    simpa only [d316248, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35385 (p : Pattern) (guard : d316249 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316248 p = 1 := by simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35384 p hg
    simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285885 p = 1 := by simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35156 p hg
    simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35386 (p : Pattern) (guard : d316250 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316249 p = 1 := by simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35385 p hg
    simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35387 (p : Pattern) (guard : d316251 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316250 p = 1 := by simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35386 p hg
    simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35388 (p : Pattern) (guard : d316252 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316251 p = 1 := by simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35387 p hg
    simpa only [d316252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35389 (p : Pattern) (guard : d316253 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316252 p = 1 := by simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35388 p hg
    simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285889 p = 1 := by simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35160 p hg
    simpa only [d316253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35390 (p : Pattern) (guard : d316254 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316253 p = 1 := by simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35389 p hg
    simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35391 (p : Pattern) (guard : d286014 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35156 p hg
    simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35392 (p : Pattern) (guard : d286015 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286014 p = 1 := by simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35391 p hg
    simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35393 (p : Pattern) (guard : d286016 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286015 p = 1 := by simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35392 p hg
    simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35394 (p : Pattern) (guard : d286017 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286016 p = 1 := by simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35393 p hg
    simpa only [d286017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35395 (p : Pattern) (guard : d286018 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286017 p = 1 := by simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35394 p hg
    simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35396 (p : Pattern) (guard : d286019 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d286018 p = 1 := by simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35395 p hg
    simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35397 (p : Pattern) (guard : d316255 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316254 p = 1 := by simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35390 p hg
    simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286019 p = 1 := by simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35396 p hg
    simpa only [d316255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35398 (p : Pattern) (guard : d316256 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d285977 p = 1 := by simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35378 p hg
    simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316255 p = 1 := by simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35397 p hg
    simpa only [d316256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35399 (p : Pattern) (guard : d316257 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d285971 p = 1 := by simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35372 p hg
    simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316256 p = 1 := by simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35398 p hg
    simpa only [d316257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35400 (p : Pattern) (guard : d286024 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285966 p = 1 := by simpa only [d286024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35302 p hg
    simpa only [d286024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35401 (p : Pattern) (guard : d286025 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286024 p = 1 := by simpa only [d286025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35400 p hg
    simpa only [d286025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257323 p = 1 := by simpa only [d286025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35166 p hg
    simpa only [d286025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35402 (p : Pattern) (guard : d286026 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286025 p = 1 := by simpa only [d286026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35401 p hg
    simpa only [d286026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35403 (p : Pattern) (guard : d286027 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d286026 p = 1 := by simpa only [d286027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35402 p hg
    simpa only [d286027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35404 (p : Pattern) (guard : d286028 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286027 p = 1 := by simpa only [d286028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35403 p hg
    simpa only [d286028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35405 (p : Pattern) (guard : d286029 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285973 p = 1 := by simpa only [d286029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35309 p hg
    simpa only [d286029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35406 (p : Pattern) (guard : d286030 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286029 p = 1 := by simpa only [d286030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35405 p hg
    simpa only [d286030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257328 p = 1 := by simpa only [d286030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35171 p hg
    simpa only [d286030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35407 (p : Pattern) (guard : d286031 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286030 p = 1 := by simpa only [d286031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35406 p hg
    simpa only [d286031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35408 (p : Pattern) (guard : d286032 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d286031 p = 1 := by simpa only [d286032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35407 p hg
    simpa only [d286032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35409 (p : Pattern) (guard : d316259 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316251 p = 1 := by simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35353 p hg
    simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35410 (p : Pattern) (guard : d316260 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316259 p = 1 := by simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35409 p hg
    simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285896 p = 1 := by simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35175 p hg
    simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35411 (p : Pattern) (guard : d316261 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316260 p = 1 := by simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35410 p hg
    simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35412 (p : Pattern) (guard : d286036 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286016 p = 1 := by simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35359 p hg
    simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35413 (p : Pattern) (guard : d286037 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286036 p = 1 := by simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35412 p hg
    simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35414 (p : Pattern) (guard : d286038 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d286037 p = 1 := by simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35413 p hg
    simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35415 (p : Pattern) (guard : d316262 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316261 p = 1 := by simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35411 p hg
    simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286038 p = 1 := by simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35414 p hg
    simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35416 (p : Pattern) (guard : d316263 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d286032 p = 1 := by simpa only [d316263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35408 p hg
    simpa only [d316263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316262 p = 1 := by simpa only [d316263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35415 p hg
    simpa only [d316263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35417 (p : Pattern) (guard : d316264 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d286028 p = 1 := by simpa only [d316264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35404 p hg
    simpa only [d316264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316263 p = 1 := by simpa only [d316264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35416 p hg
    simpa only [d316264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35418 (p : Pattern) (guard : d316265 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d316257 p = 1 := by simpa only [d316265, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35399 p hg
    simpa only [d316265, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316264 p = 1 := by simpa only [d316265, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35417 p hg
    simpa only [d316265, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35419 (p : Pattern) (guard : d316266 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d316258 p = 1 := by simpa only [d316266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35366 p hg
    simpa only [d316266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316265 p = 1 := by simpa only [d316266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35418 p hg
    simpa only [d316266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35420 (p : Pattern) (guard : d286044 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d285954 p = 1 := by simpa only [d286044, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35293 p hg
    simpa only [d286044, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257268 p = 1 := by simpa only [d286044, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35078 p hg
    simpa only [d286044, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35421 (p : Pattern) (guard : d286045 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d286044 p = 1 := by simpa only [d286045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35420 p hg
    simpa only [d286045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257276 p = 1 := by simpa only [d286045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35090 p hg
    simpa only [d286045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35422 (p : Pattern) (guard : d316267 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316266 p = 1 := by simpa only [d316267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35419 p hg
    simpa only [d316267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286045 p = 1 := by simpa only [d316267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35421 p hg
    simpa only [d316267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35423 (p : Pattern) (guard : d316268 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316267 p = 1 := by simpa only [d316268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35422 p hg
    simpa only [d316268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d316268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35424 (p : Pattern) (guard : d316269 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d285965 p = 1 := by simpa only [d316269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35301 p hg
    simpa only [d316269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316268 p = 1 := by simpa only [d316269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35423 p hg
    simpa only [d316269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35425 (p : Pattern) (guard : d1520 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare35426 (p : Pattern) (guard : d33554 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35425 p hg
    simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35427 (p : Pattern) (guard : d286611 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35426 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35428 (p : Pattern) (guard : d286612 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35427 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35429 (p : Pattern) (guard : d286613 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35428 p hg
    simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35430 (p : Pattern) (guard : d316227 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35429 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35192 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35431 (p : Pattern) (guard : d534 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare35432 (p : Pattern) (guard : d33559 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35431 p hg
    simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35433 (p : Pattern) (guard : d316228 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35432 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35434 (p : Pattern) (guard : d316229 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35433 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35435 (p : Pattern) (guard : d316230 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35434 p hg
    simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35436 (p : Pattern) (guard : d316231 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35435 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35437 (p : Pattern) (guard : d316232 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35430 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35436 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35438 (p : Pattern) (guard : d316233 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35437 p hg
    simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35439 (p : Pattern) (guard : d316234 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35438 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35195 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35440 (p : Pattern) (guard : d316235 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35439 p hg
    simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35441 (p : Pattern) (guard : d316236 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316235 p = 1 := by simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35440 p hg
    simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35442 (p : Pattern) (guard : d316237 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316236 p = 1 := by simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35441 p hg
    simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35443 (p : Pattern) (guard : d316238 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316237 p = 1 := by simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35442 p hg
    simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35444 (p : Pattern) (guard : d316239 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316238 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35443 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285875 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35200 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35445 (p : Pattern) (guard : d285991 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35193 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35446 (p : Pattern) (guard : d285992 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35445 p hg
    simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35447 (p : Pattern) (guard : d285993 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35446 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34960 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35448 (p : Pattern) (guard : d285994 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35447 p hg
    simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35449 (p : Pattern) (guard : d285995 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285994 p = 1 := by simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35448 p hg
    simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35450 (p : Pattern) (guard : d285996 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285995 p = 1 := by simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35449 p hg
    simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35451 (p : Pattern) (guard : d285997 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285996 p = 1 := by simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35450 p hg
    simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35452 (p : Pattern) (guard : d285998 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285997 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35451 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34969 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35453 (p : Pattern) (guard : d316240 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316239 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35444 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285998 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35452 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35454 (p : Pattern) (guard : d316241 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316240 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35453 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285877 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35202 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35455 (p : Pattern) (guard : d316242 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316241 p = 1 := by simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35454 p hg
    simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35456 (p : Pattern) (guard : d316243 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316242 p = 1 := by simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35455 p hg
    simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35457 (p : Pattern) (guard : d316244 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316243 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35456 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285880 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35205 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35458 (p : Pattern) (guard : d316245 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35457 p hg
    simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285881 p = 1 := by simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35206 p hg
    simpa only [d316245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35459 (p : Pattern) (guard : d316246 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316245 p = 1 := by simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35458 p hg
    simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d316246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35460 (p : Pattern) (guard : d316247 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316246 p = 1 := by simpa only [d316247, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35459 p hg
    simpa only [d316247, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316247, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d316247, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35461 (p : Pattern) (guard : d316248 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316248, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d316248, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316247 p = 1 := by simpa only [d316248, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35460 p hg
    simpa only [d316248, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35462 (p : Pattern) (guard : d316249 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316248 p = 1 := by simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35461 p hg
    simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285885 p = 1 := by simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35210 p hg
    simpa only [d316249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35463 (p : Pattern) (guard : d316250 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316249 p = 1 := by simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35462 p hg
    simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35464 (p : Pattern) (guard : d316251 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316250 p = 1 := by simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35463 p hg
    simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35465 (p : Pattern) (guard : d316259 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316251 p = 1 := by simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35466 (p : Pattern) (guard : d316260 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316259 p = 1 := by simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35465 p hg
    simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285896 p = 1 := by simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d316260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35467 (p : Pattern) (guard : d316261 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316260 p = 1 := by simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35466 p hg
    simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35468 (p : Pattern) (guard : d286014 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35210 p hg
    simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35469 (p : Pattern) (guard : d286015 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286014 p = 1 := by simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35468 p hg
    simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35470 (p : Pattern) (guard : d286016 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286015 p = 1 := by simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35469 p hg
    simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35471 (p : Pattern) (guard : d286036 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286016 p = 1 := by simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35470 p hg
    simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35472 (p : Pattern) (guard : d286037 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286036 p = 1 := by simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35471 p hg
    simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35473 (p : Pattern) (guard : d286038 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d286037 p = 1 := by simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35472 p hg
    simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35474 (p : Pattern) (guard : d316262 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316261 p = 1 := by simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35467 p hg
    simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286038 p = 1 := by simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35473 p hg
    simpa only [d316262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35475 (p : Pattern) (guard : d316270 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316262 p = 1 := by simpa only [d316270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35474 p hg
    simpa only [d316270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35476 (p : Pattern) (guard : d316271 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316270 p = 1 := by simpa only [d316271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35475 p hg
    simpa only [d316271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35477 (p : Pattern) (guard : d316272 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316272, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316272, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316271 p = 1 := by simpa only [d316272, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35476 p hg
    simpa only [d316272, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35478 (p : Pattern) (guard : d316273 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d316273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316272 p = 1 := by simpa only [d316273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35477 p hg
    simpa only [d316273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35479 (p : Pattern) (guard : d257272 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257214 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34987 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35480 (p : Pattern) (guard : d257273 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257272 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35479 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35481 (p : Pattern) (guard : d257274 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257273 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35480 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35482 (p : Pattern) (guard : d257275 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257274 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35481 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35483 (p : Pattern) (guard : d257490 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257275 p = 1 := by simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35482 p hg
    simpa only [d257490, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35484 (p : Pattern) (guard : d257491 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257490 p = 1 := by simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35483 p hg
    simpa only [d257491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35485 (p : Pattern) (guard : d316274 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316273 p = 1 := by simpa only [d316274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35478 p hg
    simpa only [d316274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257491 p = 1 := by simpa only [d316274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35484 p hg
    simpa only [d316274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35486 (p : Pattern) (guard : d316275 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316274 p = 1 := by simpa only [d316275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35485 p hg
    simpa only [d316275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d316275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35487 (p : Pattern) (guard : d316276 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d316275 p = 1 := by simpa only [d316276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35486 p hg
    simpa only [d316276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d316276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35488 (p : Pattern) (guard : d316277 p = 1) : d50390 p ≤ (3 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d316269 p = 1 := by simpa only [d316277, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35424 p hg
    simpa only [d316277, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316276 p = 1 := by simpa only [d316277, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35487 p hg
    simpa only [d316277, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35489 (p : Pattern) (guard : d1520 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare35490 (p : Pattern) (guard : d33554 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35489 p hg
    simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35491 (p : Pattern) (guard : d286611 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35490 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35492 (p : Pattern) (guard : d286612 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35491 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35493 (p : Pattern) (guard : d286613 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35492 p hg
    simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35494 (p : Pattern) (guard : d316227 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35230 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35495 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare35496 (p : Pattern) (guard : d33559 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35495 p hg
    simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35497 (p : Pattern) (guard : d316228 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35496 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35498 (p : Pattern) (guard : d316229 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35497 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35499 (p : Pattern) (guard : d316230 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35498 p hg
    simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
