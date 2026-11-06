import NetHack.Soko22Hazard87.Compare044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11250 (p : Pattern) (guard : d159976 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159975 p = 1 := by simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11249 p hg
    simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11251 (p : Pattern) (guard : d159977 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159976 p = 1 := by simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11250 p hg
    simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11252 (p : Pattern) (guard : d159978 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159977 p = 1 := by simpa only [d159978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11251 p hg
    simpa only [d159978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11253 (p : Pattern) (guard : d159979 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159978 p = 1 := by simpa only [d159979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11252 p hg
    simpa only [d159979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11254 (p : Pattern) (guard : d159980 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159921 p = 1 := by simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11172 p hg
    simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11255 (p : Pattern) (guard : d159981 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159980 p = 1 := by simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11254 p hg
    simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11256 (p : Pattern) (guard : d159982 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159981 p = 1 := by simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11255 p hg
    simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11257 (p : Pattern) (guard : d159983 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159982 p = 1 := by simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11256 p hg
    simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11258 (p : Pattern) (guard : d159984 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159976 p = 1 := by simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11250 p hg
    simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159983 p = 1 := by simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11257 p hg
    simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11259 (p : Pattern) (guard : d159985 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d159977 p = 1 := by simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11251 p hg
    simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159984 p = 1 := by simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11258 p hg
    simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11260 (p : Pattern) (guard : d159986 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159985 p = 1 := by simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11259 p hg
    simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11261 (p : Pattern) (guard : d159987 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159979 p = 1 := by simpa only [d159987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11253 p hg
    simpa only [d159987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159986 p = 1 := by simpa only [d159987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11260 p hg
    simpa only [d159987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11262 (p : Pattern) (guard : d159988 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159902 p = 1 := by simpa only [d159988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11153 p hg
    simpa only [d159988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11263 (p : Pattern) (guard : d159989 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159988 p = 1 := by simpa only [d159989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11262 p hg
    simpa only [d159989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11264 (p : Pattern) (guard : d159990 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159989 p = 1 := by simpa only [d159990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11263 p hg
    simpa only [d159990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159880 p = 1 := by simpa only [d159990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11129 p hg
    simpa only [d159990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11265 (p : Pattern) (guard : d159991 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159990 p = 1 := by simpa only [d159991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11264 p hg
    simpa only [d159991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11266 (p : Pattern) (guard : d159992 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159991 p = 1 := by simpa only [d159992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11265 p hg
    simpa only [d159992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11267 (p : Pattern) (guard : d159993 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159992 p = 1 := by simpa only [d159993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11266 p hg
    simpa only [d159993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11268 (p : Pattern) (guard : d159994 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159901 p = 1 := by simpa only [d159994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11152 p hg
    simpa only [d159994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11269 (p : Pattern) (guard : d159995 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159994 p = 1 := by simpa only [d159995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11268 p hg
    simpa only [d159995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11270 (p : Pattern) (guard : d159996 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159995 p = 1 := by simpa only [d159996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11269 p hg
    simpa only [d159996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11271 (p : Pattern) (guard : d159997 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159996 p = 1 := by simpa only [d159997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11270 p hg
    simpa only [d159997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159887 p = 1 := by simpa only [d159997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11136 p hg
    simpa only [d159997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11272 (p : Pattern) (guard : d159998 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159997 p = 1 := by simpa only [d159998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11271 p hg
    simpa only [d159998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11273 (p : Pattern) (guard : d159999 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159998 p = 1 := by simpa only [d159999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11272 p hg
    simpa only [d159999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d159999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11274 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4825 p hg
    simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11275 (p : Pattern) (guard : d322 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11274 p hg
    simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11276 (p : Pattern) (guard : d160000 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11275 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11277 (p : Pattern) (guard : d160001 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160000 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11276 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11278 (p : Pattern) (guard : d160002 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160001 p = 1 := by simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159892 p = 1 := by simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11143 p hg
    simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11279 (p : Pattern) (guard : d160003 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160003, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160003, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160002 p = 1 := by simpa only [d160003, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11278 p hg
    simpa only [d160003, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11280 (p : Pattern) (guard : d160004 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160004, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160004, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160003 p = 1 := by simpa only [d160004, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11279 p hg
    simpa only [d160004, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11281 (p : Pattern) (guard : d160005 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160004 p = 1 := by simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11280 p hg
    simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159895 p = 1 := by simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11146 p hg
    simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11282 (p : Pattern) (guard : d160006 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160005 p = 1 := by simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11281 p hg
    simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159896 p = 1 := by simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11147 p hg
    simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11283 (p : Pattern) (guard : d160007 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160006 p = 1 := by simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11282 p hg
    simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11284 (p : Pattern) (guard : d160008 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160007 p = 1 := by simpa only [d160008, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11283 p hg
    simpa only [d160008, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160008, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160008, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11285 (p : Pattern) (guard : d160009 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160009, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160009, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160008 p = 1 := by simpa only [d160009, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11284 p hg
    simpa only [d160009, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11286 (p : Pattern) (guard : d160010 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160009 p = 1 := by simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11285 p hg
    simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159900 p = 1 := by simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11151 p hg
    simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11287 (p : Pattern) (guard : d160011 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160010 p = 1 := by simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11286 p hg
    simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11288 (p : Pattern) (guard : d160012 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160011 p = 1 := by simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11287 p hg
    simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11289 (p : Pattern) (guard : d160013 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160012 p = 1 := by simpa only [d160013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11288 p hg
    simpa only [d160013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11290 (p : Pattern) (guard : d160014 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160013 p = 1 := by simpa only [d160014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d160014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159904 p = 1 := by simpa only [d160014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11155 p hg
    simpa only [d160014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11291 (p : Pattern) (guard : d160015 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160014 p = 1 := by simpa only [d160015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11290 p hg
    simpa only [d160015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11292 (p : Pattern) (guard : d160016 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159900 p = 1 := by simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11151 p hg
    simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11293 (p : Pattern) (guard : d160017 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160016 p = 1 := by simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11292 p hg
    simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11294 (p : Pattern) (guard : d160018 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160017 p = 1 := by simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11293 p hg
    simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11295 (p : Pattern) (guard : d160019 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160018 p = 1 := by simpa only [d160019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11294 p hg
    simpa only [d160019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11296 (p : Pattern) (guard : d160020 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160019 p = 1 := by simpa only [d160020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11295 p hg
    simpa only [d160020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11297 (p : Pattern) (guard : d160021 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160020 p = 1 := by simpa only [d160021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11296 p hg
    simpa only [d160021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11298 (p : Pattern) (guard : d160022 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160015 p = 1 := by simpa only [d160022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11291 p hg
    simpa only [d160022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160021 p = 1 := by simpa only [d160022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11297 p hg
    simpa only [d160022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11299 (p : Pattern) (guard : d160023 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d159999 p = 1 := by simpa only [d160023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11273 p hg
    simpa only [d160023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160022 p = 1 := by simpa only [d160023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11298 p hg
    simpa only [d160023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11300 (p : Pattern) (guard : d160024 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d159993 p = 1 := by simpa only [d160024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11267 p hg
    simpa only [d160024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160023 p = 1 := by simpa only [d160024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11299 p hg
    simpa only [d160024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11301 (p : Pattern) (guard : d160025 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160024 p = 1 := by simpa only [d160025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11300 p hg
    simpa only [d160025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11302 (p : Pattern) (guard : d160026 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159988 p = 1 := by simpa only [d160026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11262 p hg
    simpa only [d160026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11303 (p : Pattern) (guard : d160027 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160026 p = 1 := by simpa only [d160027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11302 p hg
    simpa only [d160027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159911 p = 1 := by simpa only [d160027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11162 p hg
    simpa only [d160027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11304 (p : Pattern) (guard : d160028 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160027 p = 1 := by simpa only [d160028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11303 p hg
    simpa only [d160028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11305 (p : Pattern) (guard : d160029 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160028 p = 1 := by simpa only [d160029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11304 p hg
    simpa only [d160029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11306 (p : Pattern) (guard : d160030 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160029 p = 1 := by simpa only [d160030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11305 p hg
    simpa only [d160030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11307 (p : Pattern) (guard : d160031 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159995 p = 1 := by simpa only [d160031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11269 p hg
    simpa only [d160031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11308 (p : Pattern) (guard : d160032 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160031 p = 1 := by simpa only [d160032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11307 p hg
    simpa only [d160032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159916 p = 1 := by simpa only [d160032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11167 p hg
    simpa only [d160032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11309 (p : Pattern) (guard : d160033 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160032 p = 1 := by simpa only [d160033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11308 p hg
    simpa only [d160033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11310 (p : Pattern) (guard : d160034 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160033 p = 1 := by simpa only [d160034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11309 p hg
    simpa only [d160034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11311 (p : Pattern) (guard : d160035 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160012 p = 1 := by simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11288 p hg
    simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11312 (p : Pattern) (guard : d160036 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160035 p = 1 := by simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11311 p hg
    simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159920 p = 1 := by simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11171 p hg
    simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11313 (p : Pattern) (guard : d160037 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160036 p = 1 := by simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11312 p hg
    simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11314 (p : Pattern) (guard : d160038 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160018 p = 1 := by simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11294 p hg
    simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11315 (p : Pattern) (guard : d160039 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160038 p = 1 := by simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11314 p hg
    simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11316 (p : Pattern) (guard : d160040 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160039 p = 1 := by simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11315 p hg
    simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11317 (p : Pattern) (guard : d160041 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160037 p = 1 := by simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11313 p hg
    simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160040 p = 1 := by simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11316 p hg
    simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11318 (p : Pattern) (guard : d160042 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160034 p = 1 := by simpa only [d160042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d160042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160041 p = 1 := by simpa only [d160042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11317 p hg
    simpa only [d160042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11319 (p : Pattern) (guard : d160043 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160030 p = 1 := by simpa only [d160043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11306 p hg
    simpa only [d160043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160042 p = 1 := by simpa only [d160043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11318 p hg
    simpa only [d160043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11320 (p : Pattern) (guard : d160044 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160024 p = 1 := by simpa only [d160044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11300 p hg
    simpa only [d160044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160043 p = 1 := by simpa only [d160044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11319 p hg
    simpa only [d160044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11321 (p : Pattern) (guard : d160045 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160025 p = 1 := by simpa only [d160045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11301 p hg
    simpa only [d160045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160044 p = 1 := by simpa only [d160045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11320 p hg
    simpa only [d160045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11322 (p : Pattern) (guard : d160046 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159976 p = 1 := by simpa only [d160046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11250 p hg
    simpa only [d160046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159867 p = 1 := by simpa only [d160046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11116 p hg
    simpa only [d160046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11323 (p : Pattern) (guard : d160047 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160046 p = 1 := by simpa only [d160047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11322 p hg
    simpa only [d160047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159875 p = 1 := by simpa only [d160047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11124 p hg
    simpa only [d160047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11324 (p : Pattern) (guard : d160048 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160045 p = 1 := by simpa only [d160048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11321 p hg
    simpa only [d160048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160047 p = 1 := by simpa only [d160048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11323 p hg
    simpa only [d160048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11325 (p : Pattern) (guard : d160049 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160048 p = 1 := by simpa only [d160049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11324 p hg
    simpa only [d160049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11326 (p : Pattern) (guard : d160050 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d159987 p = 1 := by simpa only [d160050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11261 p hg
    simpa only [d160050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160049 p = 1 := by simpa only [d160050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11325 p hg
    simpa only [d160050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11327 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4898 p hg
    simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11328 (p : Pattern) (guard : d322 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11327 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11329 (p : Pattern) (guard : d160000 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11328 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11330 (p : Pattern) (guard : d160001 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160000 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11329 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11331 (p : Pattern) (guard : d160002 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160001 p = 1 := by simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11330 p hg
    simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159892 p = 1 := by simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11187 p hg
    simpa only [d160002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11332 (p : Pattern) (guard : d160003 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160003, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160003, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160002 p = 1 := by simpa only [d160003, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11331 p hg
    simpa only [d160003, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11333 (p : Pattern) (guard : d160004 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160004, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160004, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160003 p = 1 := by simpa only [d160004, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11332 p hg
    simpa only [d160004, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11334 (p : Pattern) (guard : d160005 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160004 p = 1 := by simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11333 p hg
    simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159895 p = 1 := by simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11190 p hg
    simpa only [d160005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11335 (p : Pattern) (guard : d160006 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160005 p = 1 := by simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11334 p hg
    simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159896 p = 1 := by simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11191 p hg
    simpa only [d160006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11336 (p : Pattern) (guard : d160007 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160006 p = 1 := by simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11335 p hg
    simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11337 (p : Pattern) (guard : d160008 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160007 p = 1 := by simpa only [d160008, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11336 p hg
    simpa only [d160008, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160008, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160008, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11338 (p : Pattern) (guard : d160009 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160009, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160009, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160008 p = 1 := by simpa only [d160009, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11337 p hg
    simpa only [d160009, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11339 (p : Pattern) (guard : d160010 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160009 p = 1 := by simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11338 p hg
    simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159900 p = 1 := by simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11195 p hg
    simpa only [d160010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11340 (p : Pattern) (guard : d160011 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160010 p = 1 := by simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11339 p hg
    simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11341 (p : Pattern) (guard : d160012 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160011 p = 1 := by simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11340 p hg
    simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11342 (p : Pattern) (guard : d160035 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160012 p = 1 := by simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11341 p hg
    simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11343 (p : Pattern) (guard : d160036 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160035 p = 1 := by simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11342 p hg
    simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159920 p = 1 := by simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11199 p hg
    simpa only [d160036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11344 (p : Pattern) (guard : d160037 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160036 p = 1 := by simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11343 p hg
    simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11345 (p : Pattern) (guard : d160016 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159900 p = 1 := by simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11195 p hg
    simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11346 (p : Pattern) (guard : d160017 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160016 p = 1 := by simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11345 p hg
    simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11347 (p : Pattern) (guard : d160018 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160017 p = 1 := by simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11346 p hg
    simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11348 (p : Pattern) (guard : d160038 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160018 p = 1 := by simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11347 p hg
    simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11349 (p : Pattern) (guard : d160039 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160038 p = 1 := by simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11348 p hg
    simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11350 (p : Pattern) (guard : d160040 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160039 p = 1 := by simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11349 p hg
    simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11351 (p : Pattern) (guard : d160041 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160037 p = 1 := by simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11344 p hg
    simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160040 p = 1 := by simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11350 p hg
    simpa only [d160041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11352 (p : Pattern) (guard : d160051 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160041 p = 1 := by simpa only [d160051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11351 p hg
    simpa only [d160051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11353 (p : Pattern) (guard : d160052 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160051 p = 1 := by simpa only [d160052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11352 p hg
    simpa only [d160052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11354 (p : Pattern) (guard : d160053 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160053, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160053, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160052 p = 1 := by simpa only [d160053, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11353 p hg
    simpa only [d160053, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11355 (p : Pattern) (guard : d160054 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160053 p = 1 := by simpa only [d160054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11354 p hg
    simpa only [d160054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11356 (p : Pattern) (guard : d159871 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159817 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11057 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11357 (p : Pattern) (guard : d159872 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159871 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11356 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11358 (p : Pattern) (guard : d159873 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159872 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11357 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11359 (p : Pattern) (guard : d159874 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159873 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11358 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11360 (p : Pattern) (guard : d160055 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159874 p = 1 := by simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11359 p hg
    simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11361 (p : Pattern) (guard : d160056 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160055 p = 1 := by simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11360 p hg
    simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11362 (p : Pattern) (guard : d160057 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160054 p = 1 := by simpa only [d160057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11355 p hg
    simpa only [d160057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160056 p = 1 := by simpa only [d160057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11361 p hg
    simpa only [d160057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11363 (p : Pattern) (guard : d160058 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160057 p = 1 := by simpa only [d160058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11362 p hg
    simpa only [d160058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11364 (p : Pattern) (guard : d160059 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160058 p = 1 := by simpa only [d160059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11363 p hg
    simpa only [d160059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11365 (p : Pattern) (guard : d160060 p = 1) : d47768 p ≤ (-1 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160050 p = 1 := by simpa only [d160060, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11326 p hg
    simpa only [d160060, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160059 p = 1 := by simpa only [d160060, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11364 p hg
    simpa only [d160060, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11366 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318 p = 1 := by simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4955 p hg
    simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11367 (p : Pattern) (guard : d413 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11366 p hg
    simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d319 p = 1 := by simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4957 p hg
    simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11368 (p : Pattern) (guard : d414 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d413 p = 1 := by simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11367 p hg
    simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4973 p hg
    simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11369 (p : Pattern) (guard : d415 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d414 p = 1 := by simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11368 p hg
    simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11370 (p : Pattern) (guard : d160061 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d415 p = 1 := by simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11369 p hg
    simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11371 (p : Pattern) (guard : d160062 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160061 p = 1 := by simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11370 p hg
    simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11372 (p : Pattern) (guard : d160063 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160062 p = 1 := by simpa only [d160063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11371 p hg
    simpa only [d160063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159942 p = 1 := by simpa only [d160063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d160063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11373 (p : Pattern) (guard : d160064 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160064, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160064, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160063 p = 1 := by simpa only [d160064, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11372 p hg
    simpa only [d160064, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11374 (p : Pattern) (guard : d160065 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160065, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160065, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160064 p = 1 := by simpa only [d160065, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11373 p hg
    simpa only [d160065, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11375 (p : Pattern) (guard : d160066 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160065 p = 1 := by simpa only [d160066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11374 p hg
    simpa only [d160066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159945 p = 1 := by simpa only [d160066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11219 p hg
    simpa only [d160066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11376 (p : Pattern) (guard : d160067 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160066 p = 1 := by simpa only [d160067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11375 p hg
    simpa only [d160067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159946 p = 1 := by simpa only [d160067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11220 p hg
    simpa only [d160067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11377 (p : Pattern) (guard : d160068 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160067 p = 1 := by simpa only [d160068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11376 p hg
    simpa only [d160068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11378 (p : Pattern) (guard : d160069 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160068 p = 1 := by simpa only [d160069, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11377 p hg
    simpa only [d160069, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160069, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160069, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11379 (p : Pattern) (guard : d160070 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160070, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160070, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160069 p = 1 := by simpa only [d160070, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11378 p hg
    simpa only [d160070, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11380 (p : Pattern) (guard : d160071 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160070 p = 1 := by simpa only [d160071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11379 p hg
    simpa only [d160071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159950 p = 1 := by simpa only [d160071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11224 p hg
    simpa only [d160071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11381 (p : Pattern) (guard : d160072 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160071 p = 1 := by simpa only [d160072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11380 p hg
    simpa only [d160072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11382 (p : Pattern) (guard : d160073 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160072 p = 1 := by simpa only [d160073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11381 p hg
    simpa only [d160073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11383 (p : Pattern) (guard : d160074 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160073 p = 1 := by simpa only [d160074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11382 p hg
    simpa only [d160074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11384 (p : Pattern) (guard : d160075 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160074 p = 1 := by simpa only [d160075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11383 p hg
    simpa only [d160075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159954 p = 1 := by simpa only [d160075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d160075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11385 (p : Pattern) (guard : d160076 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160075 p = 1 := by simpa only [d160076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11384 p hg
    simpa only [d160076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11386 (p : Pattern) (guard : d160077 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159950 p = 1 := by simpa only [d160077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11224 p hg
    simpa only [d160077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11387 (p : Pattern) (guard : d160078 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160077 p = 1 := by simpa only [d160078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11386 p hg
    simpa only [d160078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11388 (p : Pattern) (guard : d160079 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160078 p = 1 := by simpa only [d160079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11387 p hg
    simpa only [d160079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11389 (p : Pattern) (guard : d160080 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160079 p = 1 := by simpa only [d160080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11388 p hg
    simpa only [d160080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11390 (p : Pattern) (guard : d160081 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160080 p = 1 := by simpa only [d160081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11389 p hg
    simpa only [d160081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11391 (p : Pattern) (guard : d160082 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160081 p = 1 := by simpa only [d160082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11390 p hg
    simpa only [d160082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11392 (p : Pattern) (guard : d160083 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160076 p = 1 := by simpa only [d160083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11385 p hg
    simpa only [d160083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160082 p = 1 := by simpa only [d160083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11391 p hg
    simpa only [d160083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11393 (p : Pattern) (guard : d160084 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160083 p = 1 := by simpa only [d160084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11392 p hg
    simpa only [d160084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11394 (p : Pattern) (guard : d160085 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160084 p = 1 := by simpa only [d160085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11393 p hg
    simpa only [d160085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11395 (p : Pattern) (guard : d160086 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160086, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160086, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160085 p = 1 := by simpa only [d160086, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11394 p hg
    simpa only [d160086, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11396 (p : Pattern) (guard : d160087 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160086 p = 1 := by simpa only [d160087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11395 p hg
    simpa only [d160087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11397 (p : Pattern) (guard : d160088 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159847 p = 1 := by simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11095 p hg
    simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11398 (p : Pattern) (guard : d160089 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160088 p = 1 := by simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11397 p hg
    simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11399 (p : Pattern) (guard : d160090 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160089 p = 1 := by simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11398 p hg
    simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11400 (p : Pattern) (guard : d160091 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160090 p = 1 := by simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11399 p hg
    simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11401 (p : Pattern) (guard : d160092 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160091 p = 1 := by simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11400 p hg
    simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11402 (p : Pattern) (guard : d160093 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160092 p = 1 := by simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11401 p hg
    simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11403 (p : Pattern) (guard : d160094 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160087 p = 1 := by simpa only [d160094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11396 p hg
    simpa only [d160094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160093 p = 1 := by simpa only [d160094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11402 p hg
    simpa only [d160094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11404 (p : Pattern) (guard : d160095 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160094 p = 1 := by simpa only [d160095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11403 p hg
    simpa only [d160095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11405 (p : Pattern) (guard : d160096 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160095 p = 1 := by simpa only [d160096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11404 p hg
    simpa only [d160096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11406 (p : Pattern) (guard : d160097 p = 1) : d47865 p ≤ (-1 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160096 p = 1 := by simpa only [d160097, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11405 p hg
    simpa only [d160097, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160097, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d160097, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11407 (p : Pattern) (guard : d160098 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d160060 p = 1 := by simpa only [d160098, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11365 p hg
    simpa only [d160098, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160097 p = 1 := by simpa only [d160098, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11406 p hg
    simpa only [d160098, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11408 (p : Pattern) (guard : d160099 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160098 p = 1 := by simpa only [d160099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11407 p hg
    simpa only [d160099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11409 (p : Pattern) (guard : d160100 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160099 p = 1 := by simpa only [d160100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11408 p hg
    simpa only [d160100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11410 (p : Pattern) (guard : d160101 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160100 p = 1 := by simpa only [d160101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11409 p hg
    simpa only [d160101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11411 (p : Pattern) (guard : d160102 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160101 p = 1 := by simpa only [d160102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11410 p hg
    simpa only [d160102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11412 (p : Pattern) (guard : d160103 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160102 p = 1 := by simpa only [d160103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11411 p hg
    simpa only [d160103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11413 (p : Pattern) (guard : d160104 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160103 p = 1 := by simpa only [d160104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11412 p hg
    simpa only [d160104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11414 (p : Pattern) (guard : d160105 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d159972 p = 1 := by simpa only [d160105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11246 p hg
    simpa only [d160105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160104 p = 1 := by simpa only [d160105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11413 p hg
    simpa only [d160105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11415 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5386 p hg
    simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11416 (p : Pattern) (guard : d754 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11415 p hg
    simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11417 (p : Pattern) (guard : d160106 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11416 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11418 (p : Pattern) (guard : d160107 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160106 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11417 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11419 (p : Pattern) (guard : d160108 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160001 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160107 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11418 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11420 (p : Pattern) (guard : d160109 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160108 p = 1 := by simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11419 p hg
    simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11421 (p : Pattern) (guard : d160110 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160109 p = 1 := by simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11420 p hg
    simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11422 (p : Pattern) (guard : d160111 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160107 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11418 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11423 (p : Pattern) (guard : d160112 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160111 p = 1 := by simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11422 p hg
    simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11424 (p : Pattern) (guard : d160113 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160112 p = 1 := by simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11423 p hg
    simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11425 (p : Pattern) (guard : d160114 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160110 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11421 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160113 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11424 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11426 (p : Pattern) (guard : d160115 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160113 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11424 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11427 (p : Pattern) (guard : d160116 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160114 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11425 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160115 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11428 (p : Pattern) (guard : d160117 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160116 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11427 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11429 (p : Pattern) (guard : d160118 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160117 p = 1 := by simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11428 p hg
    simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11430 (p : Pattern) (guard : d160119 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160118 p = 1 := by simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11429 p hg
    simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11431 (p : Pattern) (guard : d160120 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160115 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11432 (p : Pattern) (guard : d160121 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160120 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11431 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11433 (p : Pattern) (guard : d160122 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160121 p = 1 := by simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11432 p hg
    simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11434 (p : Pattern) (guard : d160123 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160122 p = 1 := by simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11433 p hg
    simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11435 (p : Pattern) (guard : d160124 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160119 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11430 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160123 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11434 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11436 (p : Pattern) (guard : d160125 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160124 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11435 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11437 (p : Pattern) (guard : d160126 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160125 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11438 (p : Pattern) (guard : d160127 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160126 p = 1 := by simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11437 p hg
    simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11439 (p : Pattern) (guard : d160128 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160123 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11434 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11440 (p : Pattern) (guard : d160129 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160128 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11439 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11441 (p : Pattern) (guard : d160130 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160129 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11440 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11442 (p : Pattern) (guard : d160131 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160130 p = 1 := by simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11441 p hg
    simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11443 (p : Pattern) (guard : d160132 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160127 p = 1 := by simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11438 p hg
    simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160131 p = 1 := by simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11442 p hg
    simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11444 (p : Pattern) (guard : d160133 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160132 p = 1 := by simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11443 p hg
    simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11445 (p : Pattern) (guard : d160134 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160133 p = 1 := by simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11444 p hg
    simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11446 (p : Pattern) (guard : d160135 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160134 p = 1 := by simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11445 p hg
    simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11447 (p : Pattern) (guard : d160136 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160135 p = 1 := by simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11446 p hg
    simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11448 (p : Pattern) (guard : d160137 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160136 p = 1 := by simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11447 p hg
    simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11449 (p : Pattern) (guard : d160138 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160137 p = 1 := by simpa only [d160138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11448 p hg
    simpa only [d160138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11450 (p : Pattern) (guard : d160139 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160138 p = 1 := by simpa only [d160139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11449 p hg
    simpa only [d160139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11451 (p : Pattern) (guard : d160140 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160126 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11437 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11452 (p : Pattern) (guard : d160141 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160130 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11441 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11453 (p : Pattern) (guard : d160142 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160140 p = 1 := by simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11451 p hg
    simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160141 p = 1 := by simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11454 (p : Pattern) (guard : d160143 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160142 p = 1 := by simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11453 p hg
    simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11455 (p : Pattern) (guard : d160144 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160143 p = 1 := by simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11454 p hg
    simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11456 (p : Pattern) (guard : d160145 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160144 p = 1 := by simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11455 p hg
    simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11457 (p : Pattern) (guard : d160146 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160145 p = 1 := by simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11456 p hg
    simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11458 (p : Pattern) (guard : d160147 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160136 p = 1 := by simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11447 p hg
    simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160146 p = 1 := by simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11457 p hg
    simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11459 (p : Pattern) (guard : d160148 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160137 p = 1 := by simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11448 p hg
    simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160147 p = 1 := by simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11460 (p : Pattern) (guard : d160149 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160148 p = 1 := by simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11461 (p : Pattern) (guard : d160150 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160139 p = 1 := by simpa only [d160150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11450 p hg
    simpa only [d160150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160149 p = 1 := by simpa only [d160150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11460 p hg
    simpa only [d160150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11462 (p : Pattern) (guard : d160151 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160125 p = 1 := by simpa only [d160151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d160151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11463 (p : Pattern) (guard : d160152 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160151 p = 1 := by simpa only [d160152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d160152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11464 (p : Pattern) (guard : d160153 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160129 p = 1 := by simpa only [d160153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11440 p hg
    simpa only [d160153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11465 (p : Pattern) (guard : d160154 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160153 p = 1 := by simpa only [d160154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11464 p hg
    simpa only [d160154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11466 (p : Pattern) (guard : d160155 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160152 p = 1 := by simpa only [d160155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11463 p hg
    simpa only [d160155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160154 p = 1 := by simpa only [d160155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11465 p hg
    simpa only [d160155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11467 (p : Pattern) (guard : d160156 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160155 p = 1 := by simpa only [d160156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11466 p hg
    simpa only [d160156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11468 (p : Pattern) (guard : d160157 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160156 p = 1 := by simpa only [d160157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d160157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11469 (p : Pattern) (guard : d160158 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160157 p = 1 := by simpa only [d160158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11468 p hg
    simpa only [d160158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11470 (p : Pattern) (guard : d160159 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160124 p = 1 := by simpa only [d160159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11435 p hg
    simpa only [d160159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11471 (p : Pattern) (guard : d160160 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160159 p = 1 := by simpa only [d160160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11470 p hg
    simpa only [d160160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11472 (p : Pattern) (guard : d160161 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160160 p = 1 := by simpa only [d160161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d160161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11473 (p : Pattern) (guard : d160162 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160128 p = 1 := by simpa only [d160162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11439 p hg
    simpa only [d160162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11474 (p : Pattern) (guard : d160163 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160162 p = 1 := by simpa only [d160163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11473 p hg
    simpa only [d160163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11475 (p : Pattern) (guard : d160164 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160163 p = 1 := by simpa only [d160164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11474 p hg
    simpa only [d160164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11476 (p : Pattern) (guard : d160165 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160161 p = 1 := by simpa only [d160165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11472 p hg
    simpa only [d160165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160164 p = 1 := by simpa only [d160165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11475 p hg
    simpa only [d160165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11477 (p : Pattern) (guard : d160166 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160165 p = 1 := by simpa only [d160166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11476 p hg
    simpa only [d160166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11478 (p : Pattern) (guard : d160167 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160166 p = 1 := by simpa only [d160167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11477 p hg
    simpa only [d160167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11479 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d545, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d545, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11480 (p : Pattern) (guard : d546 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11479 p hg
    simpa only [d546, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d546, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11481 (p : Pattern) (guard : d160168 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d546 p = 1 := by simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d160168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11482 (p : Pattern) (guard : d160169 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160168 p = 1 := by simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11481 p hg
    simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11483 (p : Pattern) (guard : d160170 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160169 p = 1 := by simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160001 p = 1 := by simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d160170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11484 (p : Pattern) (guard : d160171 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160171, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160171, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160170 p = 1 := by simpa only [d160171, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11483 p hg
    simpa only [d160171, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11485 (p : Pattern) (guard : d160172 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160172, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160172, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160171 p = 1 := by simpa only [d160172, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11484 p hg
    simpa only [d160172, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11486 (p : Pattern) (guard : d160173 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160172 p = 1 := by simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11485 p hg
    simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160110 p = 1 := by simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11421 p hg
    simpa only [d160173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11487 (p : Pattern) (guard : d160174 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160173 p = 1 := by simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11486 p hg
    simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160114 p = 1 := by simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11425 p hg
    simpa only [d160174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11488 (p : Pattern) (guard : d160175 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160174 p = 1 := by simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11487 p hg
    simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11489 (p : Pattern) (guard : d160176 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160175 p = 1 := by simpa only [d160176, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d160176, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160176, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160176, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11490 (p : Pattern) (guard : d160177 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160177, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160177, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160176 p = 1 := by simpa only [d160177, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11489 p hg
    simpa only [d160177, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11491 (p : Pattern) (guard : d160178 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160177 p = 1 := by simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11490 p hg
    simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160119 p = 1 := by simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11430 p hg
    simpa only [d160178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11492 (p : Pattern) (guard : d160179 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160178 p = 1 := by simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11491 p hg
    simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11493 (p : Pattern) (guard : d160180 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160179 p = 1 := by simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11492 p hg
    simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11494 (p : Pattern) (guard : d160181 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160180 p = 1 := by simpa only [d160181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11493 p hg
    simpa only [d160181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11495 (p : Pattern) (guard : d160182 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160181 p = 1 := by simpa only [d160182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11494 p hg
    simpa only [d160182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160127 p = 1 := by simpa only [d160182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11438 p hg
    simpa only [d160182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11496 (p : Pattern) (guard : d160183 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160182 p = 1 := by simpa only [d160183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d160183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11497 (p : Pattern) (guard : d160184 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160119 p = 1 := by simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11430 p hg
    simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11498 (p : Pattern) (guard : d160185 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160184 p = 1 := by simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11497 p hg
    simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11499 (p : Pattern) (guard : d160186 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160185 p = 1 := by simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11498 p hg
    simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160186, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
