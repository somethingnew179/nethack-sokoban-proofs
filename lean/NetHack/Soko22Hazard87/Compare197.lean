import NetHack.Soko22Hazard87.Compare196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49250 (p : Pattern) (guard : d47067 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47066 p = 1 := by simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49249 p hg
    simpa only [d47067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49251 (p : Pattern) (guard : d47068 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 89 with
  | false =>
    have hg : d47067 p = 1 := by simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49250 p hg
    simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49252 (p : Pattern) (guard : d47069 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47068 p = 1 := by simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49251 p hg
    simpa only [d47069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49253 (p : Pattern) (guard : d47070 p = 1) : d50674 p ≤ (1 : Int) + d371189 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49144 p hg
    simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47069 p = 1 := by simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49252 p hg
    simpa only [d47070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49254 (p : Pattern) (guard : d47080 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47080, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47080, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47070 p = 1 := by simpa only [d47080, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49253 p hg
    simpa only [d47080, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49255 (p : Pattern) (guard : d47081 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49143 p hg
    simpa only [d47081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47080 p = 1 := by simpa only [d47081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49254 p hg
    simpa only [d47081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49256 (p : Pattern) (guard : d321700 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  cases selected : p 69 with
  | false =>
    have hg : d321699 p = 1 := by simpa only [d321700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49244 p hg
    simpa only [d321700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47081 p = 1 := by simpa only [d321700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49255 p hg
    simpa only [d321700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49257 (p : Pattern) (guard : d321701 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  cases selected : p 51 with
  | false =>
    have hg : d321700 p = 1 := by simpa only [d321701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49256 p hg
    simpa only [d321701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49143 p hg
    simpa only [d321701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49258 (p : Pattern) (guard : d321702 p = 1) : d50675 p ≤ (1 : Int) + d371190 p := by
  cases selected : p 50 with
  | false =>
    have hg : d321701 p = 1 := by simpa only [d321702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49257 p hg
    simpa only [d321702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49143 p hg
    simpa only [d321702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49259 (p : Pattern) (guard : d321703 p = 1) : d50676 p ≤ (1 : Int) + d371191 p := by
  cases selected : p 49 with
  | false =>
    have hg : d321695 p = 1 := by simpa only [d321703, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49142 p hg
    simpa only [d321703, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321702 p = 1 := by simpa only [d321703, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49258 p hg
    simpa only [d321703, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49260 (p : Pattern) (guard : d0 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49261 (p : Pattern) (guard : d0 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49262 (p : Pattern) (guard : d0 p = 1) : d50712 p ≤ (1 : Int) + d371229 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49263 (p : Pattern) (guard : d0 p = 1) : d50724 p ≤ (1 : Int) + d371243 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49264 (p : Pattern) (guard : d0 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49265 (p : Pattern) (guard : d0 p = 1) : d50725 p ≤ (1 : Int) + d371247 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49266 (p : Pattern) (guard : d0 p = 1) : d50560 p ≤ (1 : Int) + d371048 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49267 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49268 (p : Pattern) (guard : d0 p = 1) : d49316 p ≤ (1 : Int) + d370969 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49269 (p : Pattern) (guard : d44880 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare49270 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49271 (p : Pattern) (guard : d46864 p = 1) : d47630 p ≤ (1 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49269 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49270 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49272 (p : Pattern) (guard : d46865 p = 1) : d47630 p ≤ (1 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49271 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49267 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49273 (p : Pattern) (guard : d0 p = 1) : d49310 p ≤ (1 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49274 (p : Pattern) (guard : d46866 p = 1) : d49311 p ≤ (1 : Int) + d370967 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49272 p hg
    simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49273 p hg
    simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49275 (p : Pattern) (guard : d0 p = 1) : d49315 p ≤ (1 : Int) + d370968 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49276 (p : Pattern) (guard : d46867 p = 1) : d49316 p ≤ (1 : Int) + d370969 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49274 p hg
    simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49275 p hg
    simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49277 (p : Pattern) (guard : d46868 p = 1) : d49316 p ≤ (1 : Int) + d370969 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49268 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49276 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49278 (p : Pattern) (guard : d46869 p = 1) : d50534 p ≤ (1 : Int) + d371016 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49267 p hg
    simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49277 p hg
    simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49279 (p : Pattern) (guard : d0 p = 1) : d50534 p ≤ (1 : Int) + d371016 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49280 (p : Pattern) (guard : d46870 p = 1) : d50534 p ≤ (1 : Int) + d371016 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49278 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49279 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49281 (p : Pattern) (guard : d46871 p = 1) : d49316 p ≤ (1 : Int) + d370969 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49276 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49268 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49282 (p : Pattern) (guard : d46872 p = 1) : d50534 p ≤ (1 : Int) + d371016 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49267 p hg
    simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49281 p hg
    simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49283 (p : Pattern) (guard : d46873 p = 1) : d50534 p ≤ (1 : Int) + d371016 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49282 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49279 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49284 (p : Pattern) (guard : d46874 p = 1) : d50534 p ≤ (1 : Int) + d371016 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49280 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49283 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49285 (p : Pattern) (guard : d0 p = 1) : d49317 p ≤ (1 : Int) + d370970 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49286 (p : Pattern) (guard : d46875 p = 1) : d50560 p ≤ (1 : Int) + d371048 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49284 p hg
    simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49285 p hg
    simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49287 (p : Pattern) (guard : d46876 p = 1) : d50560 p ≤ (1 : Int) + d371048 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49266 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49286 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49288 (p : Pattern) (guard : d47086 p = 1) : d50726 p ≤ (1 : Int) + d371248 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49265 p hg
    simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46876 p = 1 := by simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49287 p hg
    simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49289 (p : Pattern) (guard : d46877 p = 1) : d50727 p ≤ (1 : Int) + d371249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48991 p hg
    simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49172 p hg
    simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49290 (p : Pattern) (guard : d47087 p = 1) : d50728 p ≤ (1 : Int) + d371250 p := by
  cases selected : p 162 with
  | false =>
    have hg : d47086 p = 1 := by simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49288 p hg
    simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46877 p = 1 := by simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49289 p hg
    simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49291 (p : Pattern) (guard : d0 p = 1) : d50562 p ≤ (1 : Int) + d371050 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49292 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (1 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49293 (p : Pattern) (guard : d0 p = 1) : d49323 p ≤ (1 : Int) + d370974 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49294 (p : Pattern) (guard : d44880 p = 1) : d6 p ≤ (1 : Int) + d6 p := by
  omega
theorem compare49295 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (1 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49296 (p : Pattern) (guard : d46864 p = 1) : d47634 p ≤ (1 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49294 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49295 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49297 (p : Pattern) (guard : d46865 p = 1) : d47634 p ≤ (1 : Int) + d6 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49296 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49292 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49298 (p : Pattern) (guard : d0 p = 1) : d47963 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49299 (p : Pattern) (guard : d46866 p = 1) : d49319 p ≤ (1 : Int) + d370972 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49297 p hg
    simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49298 p hg
    simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49300 (p : Pattern) (guard : d0 p = 1) : d49322 p ≤ (1 : Int) + d370973 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49301 (p : Pattern) (guard : d46867 p = 1) : d49323 p ≤ (1 : Int) + d370974 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49299 p hg
    simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49300 p hg
    simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49302 (p : Pattern) (guard : d46868 p = 1) : d49323 p ≤ (1 : Int) + d370974 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49293 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49301 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49303 (p : Pattern) (guard : d46869 p = 1) : d50561 p ≤ (1 : Int) + d371049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49292 p hg
    simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49302 p hg
    simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49304 (p : Pattern) (guard : d0 p = 1) : d50561 p ≤ (1 : Int) + d371049 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49305 (p : Pattern) (guard : d46870 p = 1) : d50561 p ≤ (1 : Int) + d371049 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49303 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49304 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49306 (p : Pattern) (guard : d46871 p = 1) : d49323 p ≤ (1 : Int) + d370974 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49301 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49293 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49307 (p : Pattern) (guard : d46872 p = 1) : d50561 p ≤ (1 : Int) + d371049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49292 p hg
    simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49306 p hg
    simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49308 (p : Pattern) (guard : d46873 p = 1) : d50561 p ≤ (1 : Int) + d371049 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49307 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49304 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49309 (p : Pattern) (guard : d46874 p = 1) : d50561 p ≤ (1 : Int) + d371049 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49305 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49308 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49310 (p : Pattern) (guard : d0 p = 1) : d49324 p ≤ (1 : Int) + d370975 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49311 (p : Pattern) (guard : d46875 p = 1) : d50562 p ≤ (1 : Int) + d371050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49309 p hg
    simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49310 p hg
    simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49312 (p : Pattern) (guard : d46876 p = 1) : d50562 p ≤ (1 : Int) + d371050 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49291 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49311 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49313 (p : Pattern) (guard : d46877 p = 1) : d50573 p ≤ (1 : Int) + d371061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49312 p hg
    simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49314 (p : Pattern) (guard : d46878 p = 1) : d50574 p ≤ (1 : Int) + d371062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46877 p = 1 := by simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49313 p hg
    simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49315 (p : Pattern) (guard : d47088 p = 1) : d50729 p ≤ (1 : Int) + d371251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d47087 p = 1 := by simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49290 p hg
    simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46878 p = 1 := by simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49314 p hg
    simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49316 (p : Pattern) (guard : d0 p = 1) : d50732 p ≤ (1 : Int) + d371254 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49317 (p : Pattern) (guard : d47089 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d47088 p = 1 := by simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49315 p hg
    simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49316 p hg
    simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49318 (p : Pattern) (guard : d47090 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47089 p = 1 := by simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49317 p hg
    simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49319 (p : Pattern) (guard : d47091 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47090 p = 1 := by simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49318 p hg
    simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49320 (p : Pattern) (guard : d47092 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d47092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47091 p = 1 := by simpa only [d47092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49319 p hg
    simpa only [d47092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49321 (p : Pattern) (guard : d47093 p = 1) : d50734 p ≤ (1 : Int) + d371256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47093, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49263 p hg
    simpa only [d47093, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47092 p = 1 := by simpa only [d47093, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49320 p hg
    simpa only [d47093, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49322 (p : Pattern) (guard : d47094 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47094, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49262 p hg
    simpa only [d47094, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47093 p = 1 := by simpa only [d47094, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49321 p hg
    simpa only [d47094, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49323 (p : Pattern) (guard : d47095 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 159 with
  | false =>
    have hg : d47089 p = 1 := by simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49317 p hg
    simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49324 (p : Pattern) (guard : d47096 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d47090 p = 1 := by simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49318 p hg
    simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47095 p = 1 := by simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49323 p hg
    simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49325 (p : Pattern) (guard : d47097 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47091 p = 1 := by simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49319 p hg
    simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47096 p = 1 := by simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49324 p hg
    simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49326 (p : Pattern) (guard : d47098 p = 1) : d50734 p ≤ (1 : Int) + d371256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49263 p hg
    simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47097 p = 1 := by simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49325 p hg
    simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49327 (p : Pattern) (guard : d47099 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49262 p hg
    simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47098 p = 1 := by simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49326 p hg
    simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49328 (p : Pattern) (guard : d47100 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47094 p = 1 := by simpa only [d47100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49322 p hg
    simpa only [d47100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47099 p = 1 := by simpa only [d47100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49327 p hg
    simpa only [d47100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49329 (p : Pattern) (guard : d46888 p = 1) : d50560 p ≤ (1 : Int) + d371048 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49286 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49266 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49330 (p : Pattern) (guard : d47101 p = 1) : d50726 p ≤ (1 : Int) + d371248 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49265 p hg
    simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46888 p = 1 := by simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49329 p hg
    simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49331 (p : Pattern) (guard : d46889 p = 1) : d50727 p ≤ (1 : Int) + d371249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49006 p hg
    simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49172 p hg
    simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49332 (p : Pattern) (guard : d47102 p = 1) : d50728 p ≤ (1 : Int) + d371250 p := by
  cases selected : p 162 with
  | false =>
    have hg : d47101 p = 1 := by simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49330 p hg
    simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46889 p = 1 := by simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49331 p hg
    simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49333 (p : Pattern) (guard : d46888 p = 1) : d50562 p ≤ (1 : Int) + d371050 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49311 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49291 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49334 (p : Pattern) (guard : d46889 p = 1) : d50573 p ≤ (1 : Int) + d371061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49333 p hg
    simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49335 (p : Pattern) (guard : d46890 p = 1) : d50574 p ≤ (1 : Int) + d371062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46889 p = 1 := by simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49334 p hg
    simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49336 (p : Pattern) (guard : d47103 p = 1) : d50729 p ≤ (1 : Int) + d371251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d47102 p = 1 := by simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49332 p hg
    simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46890 p = 1 := by simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49335 p hg
    simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49337 (p : Pattern) (guard : d47104 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d47103 p = 1 := by simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49336 p hg
    simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49316 p hg
    simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49338 (p : Pattern) (guard : d47105 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 159 with
  | false =>
    have hg : d47104 p = 1 := by simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49337 p hg
    simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49339 (p : Pattern) (guard : d47106 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d47095 p = 1 := by simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49323 p hg
    simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47105 p = 1 := by simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49338 p hg
    simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49340 (p : Pattern) (guard : d47107 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47096 p = 1 := by simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49324 p hg
    simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47106 p = 1 := by simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49339 p hg
    simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49341 (p : Pattern) (guard : d47108 p = 1) : d50734 p ≤ (1 : Int) + d371256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49263 p hg
    simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47107 p = 1 := by simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49340 p hg
    simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49342 (p : Pattern) (guard : d47109 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49262 p hg
    simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47108 p = 1 := by simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49341 p hg
    simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49343 (p : Pattern) (guard : d47110 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47099 p = 1 := by simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49327 p hg
    simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47109 p = 1 := by simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49342 p hg
    simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49344 (p : Pattern) (guard : d47111 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 135 with
  | false =>
    have hg : d47100 p = 1 := by simpa only [d47111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49328 p hg
    simpa only [d47111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47110 p = 1 := by simpa only [d47111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49343 p hg
    simpa only [d47111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49345 (p : Pattern) (guard : d0 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49346 (p : Pattern) (guard : d47112 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47111 p = 1 := by simpa only [d47112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49344 p hg
    simpa only [d47112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d47112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49347 (p : Pattern) (guard : d0 p = 1) : d50736 p ≤ (1 : Int) + d371258 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49348 (p : Pattern) (guard : d47113 p = 1) : d50737 p ≤ (1 : Int) + d371259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47112 p = 1 := by simpa only [d47113, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49346 p hg
    simpa only [d47113, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47113, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49347 p hg
    simpa only [d47113, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49349 (p : Pattern) (guard : d47114 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47114, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d47114, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47113 p = 1 := by simpa only [d47114, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49348 p hg
    simpa only [d47114, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49350 (p : Pattern) (guard : d47115 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47109 p = 1 := by simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49342 p hg
    simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49351 (p : Pattern) (guard : d47116 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 135 with
  | false =>
    have hg : d47110 p = 1 := by simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49343 p hg
    simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47115 p = 1 := by simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49352 (p : Pattern) (guard : d47117 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47116 p = 1 := by simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49351 p hg
    simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49353 (p : Pattern) (guard : d47118 p = 1) : d50737 p ≤ (1 : Int) + d371259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47117 p = 1 := by simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49352 p hg
    simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49347 p hg
    simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49354 (p : Pattern) (guard : d47119 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47118 p = 1 := by simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49353 p hg
    simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49355 (p : Pattern) (guard : d47120 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 113 with
  | false =>
    have hg : d47114 p = 1 := by simpa only [d47120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49349 p hg
    simpa only [d47120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47119 p = 1 := by simpa only [d47120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49354 p hg
    simpa only [d47120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49356 (p : Pattern) (guard : d47121 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 96 with
  | false =>
    have hg : d47120 p = 1 := by simpa only [d47121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49355 p hg
    simpa only [d47121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49357 (p : Pattern) (guard : d47122 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 95 with
  | false =>
    have hg : d47121 p = 1 := by simpa only [d47122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49356 p hg
    simpa only [d47122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49358 (p : Pattern) (guard : d47123 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 93 with
  | false =>
    have hg : d47122 p = 1 := by simpa only [d47123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49357 p hg
    simpa only [d47123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49359 (p : Pattern) (guard : d47124 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 135 with
  | false =>
    have hg : d47115 p = 1 := by simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49350 p hg
    simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49360 (p : Pattern) (guard : d47125 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47124 p = 1 := by simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49359 p hg
    simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49361 (p : Pattern) (guard : d47126 p = 1) : d50737 p ≤ (1 : Int) + d371259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47125 p = 1 := by simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49360 p hg
    simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49347 p hg
    simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49362 (p : Pattern) (guard : d47127 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47126 p = 1 := by simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49361 p hg
    simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49363 (p : Pattern) (guard : d47128 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 113 with
  | false =>
    have hg : d47119 p = 1 := by simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49354 p hg
    simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47127 p = 1 := by simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49362 p hg
    simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49364 (p : Pattern) (guard : d47129 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 96 with
  | false =>
    have hg : d47128 p = 1 := by simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49363 p hg
    simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49365 (p : Pattern) (guard : d47130 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 95 with
  | false =>
    have hg : d47129 p = 1 := by simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49364 p hg
    simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49366 (p : Pattern) (guard : d47131 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 93 with
  | false =>
    have hg : d47130 p = 1 := by simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49365 p hg
    simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49367 (p : Pattern) (guard : d47132 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47123 p = 1 := by simpa only [d47132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49358 p hg
    simpa only [d47132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47131 p = 1 := by simpa only [d47132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49366 p hg
    simpa only [d47132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49368 (p : Pattern) (guard : d321704 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 90 with
  | false =>
    have hg : d47132 p = 1 := by simpa only [d321704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49367 p hg
    simpa only [d321704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d321704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49369 (p : Pattern) (guard : d47193 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d47090 p = 1 := by simpa only [d47193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49318 p hg
    simpa only [d47193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d47193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49370 (p : Pattern) (guard : d47194 p = 1) : d50733 p ≤ (1 : Int) + d371255 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47193 p = 1 := by simpa only [d47194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49369 p hg
    simpa only [d47194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49264 p hg
    simpa only [d47194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49371 (p : Pattern) (guard : d47195 p = 1) : d50734 p ≤ (1 : Int) + d371256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47195, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49263 p hg
    simpa only [d47195, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47194 p = 1 := by simpa only [d47195, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49370 p hg
    simpa only [d47195, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49372 (p : Pattern) (guard : d47196 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47196, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49262 p hg
    simpa only [d47196, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47195 p = 1 := by simpa only [d47196, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49371 p hg
    simpa only [d47196, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49373 (p : Pattern) (guard : d47197 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47196 p = 1 := by simpa only [d47197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49372 p hg
    simpa only [d47197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d47197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49374 (p : Pattern) (guard : d47198 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 135 with
  | false =>
    have hg : d47110 p = 1 := by simpa only [d47198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49343 p hg
    simpa only [d47198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47197 p = 1 := by simpa only [d47198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49373 p hg
    simpa only [d47198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49375 (p : Pattern) (guard : d47199 p = 1) : d50735 p ≤ (1 : Int) + d371257 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47198 p = 1 := by simpa only [d47199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49374 p hg
    simpa only [d47199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49345 p hg
    simpa only [d47199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49376 (p : Pattern) (guard : d47200 p = 1) : d50737 p ≤ (1 : Int) + d371259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47199 p = 1 := by simpa only [d47200, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49375 p hg
    simpa only [d47200, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47200, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49347 p hg
    simpa only [d47200, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49377 (p : Pattern) (guard : d47201 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47201, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d47201, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47200 p = 1 := by simpa only [d47201, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49376 p hg
    simpa only [d47201, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49378 (p : Pattern) (guard : d47202 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 113 with
  | false =>
    have hg : d47201 p = 1 := by simpa only [d47202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49377 p hg
    simpa only [d47202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49379 (p : Pattern) (guard : d47203 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 96 with
  | false =>
    have hg : d47202 p = 1 := by simpa only [d47203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49378 p hg
    simpa only [d47203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49380 (p : Pattern) (guard : d47204 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 95 with
  | false =>
    have hg : d47203 p = 1 := by simpa only [d47204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49379 p hg
    simpa only [d47204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49381 (p : Pattern) (guard : d47205 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 93 with
  | false =>
    have hg : d47204 p = 1 := by simpa only [d47205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49380 p hg
    simpa only [d47205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49382 (p : Pattern) (guard : d47206 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47205 p = 1 := by simpa only [d47206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49381 p hg
    simpa only [d47206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49383 (p : Pattern) (guard : d47207 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 90 with
  | false =>
    have hg : d47206 p = 1 := by simpa only [d47207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49382 p hg
    simpa only [d47207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49384 (p : Pattern) (guard : d321705 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 89 with
  | false =>
    have hg : d321704 p = 1 := by simpa only [d321705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49368 p hg
    simpa only [d321705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47207 p = 1 := by simpa only [d321705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49383 p hg
    simpa only [d321705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49385 (p : Pattern) (guard : d321706 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d321706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321705 p = 1 := by simpa only [d321706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49384 p hg
    simpa only [d321706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49386 (p : Pattern) (guard : d321707 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d321707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321706 p = 1 := by simpa only [d321707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49385 p hg
    simpa only [d321707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49387 (p : Pattern) (guard : d321708 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321708, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d321708, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321707 p = 1 := by simpa only [d321708, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49386 p hg
    simpa only [d321708, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49388 (p : Pattern) (guard : d321709 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49260 p hg
    simpa only [d321709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321708 p = 1 := by simpa only [d321709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49387 p hg
    simpa only [d321709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49389 (p : Pattern) (guard : d47213 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 113 with
  | false =>
    have hg : d47127 p = 1 := by simpa only [d47213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49362 p hg
    simpa only [d47213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49390 (p : Pattern) (guard : d47214 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 96 with
  | false =>
    have hg : d47213 p = 1 := by simpa only [d47214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49389 p hg
    simpa only [d47214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49391 (p : Pattern) (guard : d47215 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 95 with
  | false =>
    have hg : d47214 p = 1 := by simpa only [d47215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49390 p hg
    simpa only [d47215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49392 (p : Pattern) (guard : d47216 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 93 with
  | false =>
    have hg : d47215 p = 1 := by simpa only [d47216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49391 p hg
    simpa only [d47216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49393 (p : Pattern) (guard : d47217 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47216 p = 1 := by simpa only [d47217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49392 p hg
    simpa only [d47217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49394 (p : Pattern) (guard : d47218 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47217 p = 1 := by simpa only [d47218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49393 p hg
    simpa only [d47218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49395 (p : Pattern) (guard : d47219 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 89 with
  | false =>
    have hg : d47218 p = 1 := by simpa only [d47219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49394 p hg
    simpa only [d47219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49396 (p : Pattern) (guard : d47220 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47219 p = 1 := by simpa only [d47220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49395 p hg
    simpa only [d47220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49397 (p : Pattern) (guard : d47221 p = 1) : d50738 p ≤ (1 : Int) + d371260 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49261 p hg
    simpa only [d47221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47220 p = 1 := by simpa only [d47221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49396 p hg
    simpa only [d47221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49398 (p : Pattern) (guard : d47222 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47222, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d47222, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47221 p = 1 := by simpa only [d47222, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49397 p hg
    simpa only [d47222, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49399 (p : Pattern) (guard : d47223 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49260 p hg
    simpa only [d47223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47222 p = 1 := by simpa only [d47223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49398 p hg
    simpa only [d47223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49400 (p : Pattern) (guard : d321710 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  cases selected : p 69 with
  | false =>
    have hg : d321709 p = 1 := by simpa only [d321710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49388 p hg
    simpa only [d321710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47223 p = 1 := by simpa only [d321710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49399 p hg
    simpa only [d321710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49401 (p : Pattern) (guard : d321711 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  cases selected : p 51 with
  | false =>
    have hg : d321710 p = 1 := by simpa only [d321711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49400 p hg
    simpa only [d321711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49260 p hg
    simpa only [d321711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49402 (p : Pattern) (guard : d321712 p = 1) : d50739 p ≤ (1 : Int) + d371261 p := by
  cases selected : p 50 with
  | false =>
    have hg : d321711 p = 1 := by simpa only [d321712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49401 p hg
    simpa only [d321712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49260 p hg
    simpa only [d321712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49403 (p : Pattern) (guard : d0 p = 1) : d50821 p ≤ (1 : Int) + d371351 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49404 (p : Pattern) (guard : d321713 p = 1) : d50822 p ≤ (1 : Int) + d371352 p := by
  cases selected : p 49 with
  | false =>
    have hg : d321712 p = 1 := by simpa only [d321713, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49402 p hg
    simpa only [d321713, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321713, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49403 p hg
    simpa only [d321713, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49405 (p : Pattern) (guard : d321714 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 48 with
  | false =>
    have hg : d321703 p = 1 := by simpa only [d321714, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49259 p hg
    simpa only [d321714, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321713 p = 1 := by simpa only [d321714, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49404 p hg
    simpa only [d321714, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49406 (p : Pattern) (guard : d321715 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321714 p = 1 := by simpa only [d321715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49405 p hg
    simpa only [d321715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49407 (p : Pattern) (guard : d321716 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321715 p = 1 := by simpa only [d321716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49406 p hg
    simpa only [d321716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49408 (p : Pattern) (guard : d321717 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321716 p = 1 := by simpa only [d321717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49407 p hg
    simpa only [d321717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49409 (p : Pattern) (guard : d321718 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321717 p = 1 := by simpa only [d321718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49408 p hg
    simpa only [d321718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49410 (p : Pattern) (guard : d321719 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321718 p = 1 := by simpa only [d321719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49409 p hg
    simpa only [d321719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49411 (p : Pattern) (guard : d321720 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321719 p = 1 := by simpa only [d321720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49410 p hg
    simpa only [d321720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49412 (p : Pattern) (guard : d321721 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321720 p = 1 := by simpa only [d321721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49411 p hg
    simpa only [d321721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49413 (p : Pattern) (guard : d321722 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321721 p = 1 := by simpa only [d321722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49412 p hg
    simpa only [d321722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49414 (p : Pattern) (guard : d321723 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321722 p = 1 := by simpa only [d321723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49413 p hg
    simpa only [d321723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49415 (p : Pattern) (guard : d321724 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d321724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321723 p = 1 := by simpa only [d321724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49414 p hg
    simpa only [d321724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49416 (p : Pattern) (guard : d375125 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d375125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321724 p = 1 := by simpa only [d375125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49415 p hg
    simpa only [d375125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49417 (p : Pattern) (guard : d375126 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 260 with
  | false =>
    have hg : d375125 p = 1 := by simpa only [d375126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49416 p hg
    simpa only [d375126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49418 (p : Pattern) (guard : d375127 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 259 with
  | false =>
    have hg : d375126 p = 1 := by simpa only [d375127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49417 p hg
    simpa only [d375127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49419 (p : Pattern) (guard : d375128 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 258 with
  | false =>
    have hg : d375127 p = 1 := by simpa only [d375128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49418 p hg
    simpa only [d375128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49420 (p : Pattern) (guard : d375129 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 257 with
  | false =>
    have hg : d375128 p = 1 := by simpa only [d375129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49419 p hg
    simpa only [d375129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49421 (p : Pattern) (guard : d375130 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 256 with
  | false =>
    have hg : d375129 p = 1 := by simpa only [d375130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49420 p hg
    simpa only [d375130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49422 (p : Pattern) (guard : d375131 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 255 with
  | false =>
    have hg : d375130 p = 1 := by simpa only [d375131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49421 p hg
    simpa only [d375131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49423 (p : Pattern) (guard : d375132 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 254 with
  | false =>
    have hg : d375131 p = 1 := by simpa only [d375132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49422 p hg
    simpa only [d375132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49424 (p : Pattern) (guard : d375133 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 253 with
  | false =>
    have hg : d375132 p = 1 := by simpa only [d375133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49423 p hg
    simpa only [d375133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49425 (p : Pattern) (guard : d375134 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 252 with
  | false =>
    have hg : d375133 p = 1 := by simpa only [d375134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49424 p hg
    simpa only [d375134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49426 (p : Pattern) (guard : d375135 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 251 with
  | false =>
    have hg : d375134 p = 1 := by simpa only [d375135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49425 p hg
    simpa only [d375135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49427 (p : Pattern) (guard : d375136 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 250 with
  | false =>
    have hg : d375135 p = 1 := by simpa only [d375136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49426 p hg
    simpa only [d375136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49428 (p : Pattern) (guard : d375137 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 249 with
  | false =>
    have hg : d375136 p = 1 := by simpa only [d375137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49427 p hg
    simpa only [d375137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49429 (p : Pattern) (guard : d375138 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 245 with
  | false =>
    have hg : d375137 p = 1 := by simpa only [d375138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49428 p hg
    simpa only [d375138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49430 (p : Pattern) (guard : d375139 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 200 with
  | false =>
    have hg : d375138 p = 1 := by simpa only [d375139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49429 p hg
    simpa only [d375139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49431 (p : Pattern) (guard : d375140 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 199 with
  | false =>
    have hg : d375139 p = 1 := by simpa only [d375140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49430 p hg
    simpa only [d375140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49432 (p : Pattern) (guard : d375141 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 186 with
  | false =>
    have hg : d375140 p = 1 := by simpa only [d375141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49431 p hg
    simpa only [d375141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49433 (p : Pattern) (guard : d375142 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 185 with
  | false =>
    have hg : d375141 p = 1 := by simpa only [d375142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49432 p hg
    simpa only [d375142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49434 (p : Pattern) (guard : d375143 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 184 with
  | false =>
    have hg : d375142 p = 1 := by simpa only [d375143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49433 p hg
    simpa only [d375143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49435 (p : Pattern) (guard : d375144 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 181 with
  | false =>
    have hg : d375143 p = 1 := by simpa only [d375144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49434 p hg
    simpa only [d375144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49436 (p : Pattern) (guard : d375145 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 177 with
  | false =>
    have hg : d375144 p = 1 := by simpa only [d375145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49435 p hg
    simpa only [d375145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49437 (p : Pattern) (guard : d375146 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 164 with
  | false =>
    have hg : d375145 p = 1 := by simpa only [d375146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49436 p hg
    simpa only [d375146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49438 (p : Pattern) (guard : d375147 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 156 with
  | false =>
    have hg : d375146 p = 1 := by simpa only [d375147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49437 p hg
    simpa only [d375147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49439 (p : Pattern) (guard : d375148 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 155 with
  | false =>
    have hg : d375147 p = 1 := by simpa only [d375148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49438 p hg
    simpa only [d375148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49440 (p : Pattern) (guard : d375149 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d375148 p = 1 := by simpa only [d375149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49439 p hg
    simpa only [d375149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49441 (p : Pattern) (guard : d375150 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 133 with
  | false =>
    have hg : d375149 p = 1 := by simpa only [d375150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49440 p hg
    simpa only [d375150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49442 (p : Pattern) (guard : d375151 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 120 with
  | false =>
    have hg : d375150 p = 1 := by simpa only [d375151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49441 p hg
    simpa only [d375151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49443 (p : Pattern) (guard : d375152 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 118 with
  | false =>
    have hg : d375151 p = 1 := by simpa only [d375152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49442 p hg
    simpa only [d375152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49444 (p : Pattern) (guard : d375153 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 114 with
  | false =>
    have hg : d375152 p = 1 := by simpa only [d375153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49443 p hg
    simpa only [d375153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49445 (p : Pattern) (guard : d375154 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 111 with
  | false =>
    have hg : d375153 p = 1 := by simpa only [d375154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49444 p hg
    simpa only [d375154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49446 (p : Pattern) (guard : d375155 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 98 with
  | false =>
    have hg : d375154 p = 1 := by simpa only [d375155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49445 p hg
    simpa only [d375155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49447 (p : Pattern) (guard : d375156 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 97 with
  | false =>
    have hg : d375155 p = 1 := by simpa only [d375156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49446 p hg
    simpa only [d375156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49448 (p : Pattern) (guard : d375157 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 94 with
  | false =>
    have hg : d375156 p = 1 := by simpa only [d375157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49447 p hg
    simpa only [d375157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49449 (p : Pattern) (guard : d375158 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 76 with
  | false =>
    have hg : d375157 p = 1 := by simpa only [d375158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49448 p hg
    simpa only [d375158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49450 (p : Pattern) (guard : d375159 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 67 with
  | false =>
    have hg : d375158 p = 1 := by simpa only [d375159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49449 p hg
    simpa only [d375159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49451 (p : Pattern) (guard : d375160 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 52 with
  | false =>
    have hg : d375159 p = 1 := by simpa only [d375160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49450 p hg
    simpa only [d375160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49452 (p : Pattern) (guard : d375161 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 47 with
  | false =>
    have hg : d375160 p = 1 := by simpa only [d375161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49451 p hg
    simpa only [d375161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49453 (p : Pattern) (guard : d375162 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 46 with
  | false =>
    have hg : d375161 p = 1 := by simpa only [d375162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49452 p hg
    simpa only [d375162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49454 (p : Pattern) (guard : d375163 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 45 with
  | false =>
    have hg : d375162 p = 1 := by simpa only [d375163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49453 p hg
    simpa only [d375163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49455 (p : Pattern) (guard : d375164 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 30 with
  | false =>
    have hg : d375163 p = 1 := by simpa only [d375164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49454 p hg
    simpa only [d375164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49456 (p : Pattern) (guard : d375165 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 29 with
  | false =>
    have hg : d375164 p = 1 := by simpa only [d375165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49455 p hg
    simpa only [d375165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49457 (p : Pattern) (guard : d375166 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 28 with
  | false =>
    have hg : d375165 p = 1 := by simpa only [d375166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49456 p hg
    simpa only [d375166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49458 (p : Pattern) (guard : d375167 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 27 with
  | false =>
    have hg : d375166 p = 1 := by simpa only [d375167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49457 p hg
    simpa only [d375167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49459 (p : Pattern) (guard : d375168 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  cases selected : p 25 with
  | false =>
    have hg : d375167 p = 1 := by simpa only [d375168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49458 p hg
    simpa only [d375168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d375168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49460 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49461 (p : Pattern) (guard : d0 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49462 (p : Pattern) (guard : d0 p = 1) : d50588 p ≤ (0 : Int) + d371076 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49463 (p : Pattern) (guard : d0 p = 1) : d50546 p ≤ (0 : Int) + d371028 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49464 (p : Pattern) (guard : d0 p = 1) : d50566 p ≤ (0 : Int) + d371054 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49465 (p : Pattern) (guard : d0 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49466 (p : Pattern) (guard : d0 p = 1) : d50569 p ≤ (0 : Int) + d371057 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49467 (p : Pattern) (guard : d0 p = 1) : d50553 p ≤ (0 : Int) + d371040 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49468 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49469 (p : Pattern) (guard : d0 p = 1) : d49396 p ≤ (0 : Int) + d370984 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49470 (p : Pattern) (guard : d44880 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare49471 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49472 (p : Pattern) (guard : d46864 p = 1) : d47617 p ≤ (0 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49470 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49471 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49473 (p : Pattern) (guard : d46865 p = 1) : d47617 p ≤ (0 : Int) + d4 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49472 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49468 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49474 (p : Pattern) (guard : d0 p = 1) : d49391 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49475 (p : Pattern) (guard : d46866 p = 1) : d49392 p ≤ (0 : Int) + d370982 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49473 p hg
    simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49474 p hg
    simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49476 (p : Pattern) (guard : d0 p = 1) : d49395 p ≤ (0 : Int) + d370983 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49477 (p : Pattern) (guard : d46867 p = 1) : d49396 p ≤ (0 : Int) + d370984 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49475 p hg
    simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49476 p hg
    simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49478 (p : Pattern) (guard : d46868 p = 1) : d49396 p ≤ (0 : Int) + d370984 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49469 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49477 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49479 (p : Pattern) (guard : d46869 p = 1) : d50510 p ≤ (0 : Int) + d370985 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49468 p hg
    simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49478 p hg
    simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49480 (p : Pattern) (guard : d0 p = 1) : d50510 p ≤ (0 : Int) + d370985 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49481 (p : Pattern) (guard : d46870 p = 1) : d50510 p ≤ (0 : Int) + d370985 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49479 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49482 (p : Pattern) (guard : d46871 p = 1) : d49396 p ≤ (0 : Int) + d370984 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49477 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49469 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49483 (p : Pattern) (guard : d46872 p = 1) : d50510 p ≤ (0 : Int) + d370985 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49468 p hg
    simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49482 p hg
    simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49484 (p : Pattern) (guard : d46873 p = 1) : d50510 p ≤ (0 : Int) + d370985 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49483 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49485 (p : Pattern) (guard : d46874 p = 1) : d50510 p ≤ (0 : Int) + d370985 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49481 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49484 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49486 (p : Pattern) (guard : d0 p = 1) : d49397 p ≤ (0 : Int) + d371039 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49487 (p : Pattern) (guard : d46875 p = 1) : d50553 p ≤ (0 : Int) + d371040 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49485 p hg
    simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49486 p hg
    simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49488 (p : Pattern) (guard : d46876 p = 1) : d50553 p ≤ (0 : Int) + d371040 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49467 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49487 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49489 (p : Pattern) (guard : d0 p = 1) : d50527 p ≤ (0 : Int) + d371009 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49490 (p : Pattern) (guard : d46877 p = 1) : d50570 p ≤ (0 : Int) + d371058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49488 p hg
    simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49489 p hg
    simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49491 (p : Pattern) (guard : d0 p = 1) : d50531 p ≤ (0 : Int) + d371013 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49492 (p : Pattern) (guard : d46878 p = 1) : d50571 p ≤ (0 : Int) + d371059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46877 p = 1 := by simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49490 p hg
    simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49491 p hg
    simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49493 (p : Pattern) (guard : d46879 p = 1) : d50572 p ≤ (0 : Int) + d371060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49466 p hg
    simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46878 p = 1 := by simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49492 p hg
    simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49494 (p : Pattern) (guard : d0 p = 1) : d50575 p ≤ (0 : Int) + d371063 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49495 (p : Pattern) (guard : d46880 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46879 p = 1 := by simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49493 p hg
    simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49494 p hg
    simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49496 (p : Pattern) (guard : d46881 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49465 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46880 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49495 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49497 (p : Pattern) (guard : d46882 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49465 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46881 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49496 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49498 (p : Pattern) (guard : d46883 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46880 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49495 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49465 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49499 (p : Pattern) (guard : d46884 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46881 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49496 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46883 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49498 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
