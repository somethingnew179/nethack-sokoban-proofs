import NetHack.Soko22Hazard87.Compare178
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44750 (p : Pattern) (guard : d367093 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367092 p = 1 := by simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44748 p hg
    simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366893 p = 1 := by simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44749 p hg
    simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44751 (p : Pattern) (guard : d366894 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44752 (p : Pattern) (guard : d367094 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367093 p = 1 := by simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44750 p hg
    simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366894 p = 1 := by simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44751 p hg
    simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44753 (p : Pattern) (guard : d367095 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367094 p = 1 := by simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44752 p hg
    simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44754 (p : Pattern) (guard : d367096 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367080 p = 1 := by simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44711 p hg
    simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367095 p = 1 := by simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44755 (p : Pattern) (guard : d367097 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367091 p = 1 := by simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44740 p hg
    simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367096 p = 1 := by simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44754 p hg
    simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44756 (p : Pattern) (guard : d367098 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367082 p = 1 := by simpa only [d367098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44713 p hg
    simpa only [d367098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367097 p = 1 := by simpa only [d367098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44755 p hg
    simpa only [d367098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44757 (p : Pattern) (guard : d367099 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367099, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d367099, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367098 p = 1 := by simpa only [d367099, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44756 p hg
    simpa only [d367099, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44758 (p : Pattern) (guard : d367100 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367100, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d367100, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367099 p = 1 := by simpa only [d367100, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d367100, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44759 (p : Pattern) (guard : d366984 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32698 p = 1 := by simpa only [d366984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44167 p hg
    simpa only [d366984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d366984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44699 p hg
    simpa only [d366984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44760 (p : Pattern) (guard : d366985 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366984 p = 1 := by simpa only [d366985, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44759 p hg
    simpa only [d366985, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366985, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d366985, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44761 (p : Pattern) (guard : d366986 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34782 p = 1 := by simpa only [d366986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44660 p hg
    simpa only [d366986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366985 p = 1 := by simpa only [d366986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44760 p hg
    simpa only [d366986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44762 (p : Pattern) (guard : d366987 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366986 p = 1 := by simpa only [d366987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44761 p hg
    simpa only [d366987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44763 (p : Pattern) (guard : d366988 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366987 p = 1 := by simpa only [d366988, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44762 p hg
    simpa only [d366988, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366988, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366988, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44764 (p : Pattern) (guard : d366989 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366988 p = 1 := by simpa only [d366989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44763 p hg
    simpa only [d366989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366872 p = 1 := by simpa only [d366989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44704 p hg
    simpa only [d366989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44765 (p : Pattern) (guard : d367101 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367101, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367101, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366989 p = 1 := by simpa only [d367101, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44764 p hg
    simpa only [d367101, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44766 (p : Pattern) (guard : d366990 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44767 (p : Pattern) (guard : d367102 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367101 p = 1 := by simpa only [d367102, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44765 p hg
    simpa only [d367102, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366990 p = 1 := by simpa only [d367102, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44766 p hg
    simpa only [d367102, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44768 (p : Pattern) (guard : d366991 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44769 (p : Pattern) (guard : d367103 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367102 p = 1 := by simpa only [d367103, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44767 p hg
    simpa only [d367103, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366991 p = 1 := by simpa only [d367103, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44768 p hg
    simpa only [d367103, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44770 (p : Pattern) (guard : d367104 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367103 p = 1 := by simpa only [d367104, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44769 p hg
    simpa only [d367104, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367104, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367104, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44771 (p : Pattern) (guard : d367105 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367104 p = 1 := by simpa only [d367105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44770 p hg
    simpa only [d367105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367095 p = 1 := by simpa only [d367105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d367105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44772 (p : Pattern) (guard : d367106 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367095 p = 1 := by simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44773 (p : Pattern) (guard : d367107 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367105 p = 1 := by simpa only [d367107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44771 p hg
    simpa only [d367107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367106 p = 1 := by simpa only [d367107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44772 p hg
    simpa only [d367107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44774 (p : Pattern) (guard : d367108 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367097 p = 1 := by simpa only [d367108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44755 p hg
    simpa only [d367108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367107 p = 1 := by simpa only [d367108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44773 p hg
    simpa only [d367108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44775 (p : Pattern) (guard : d367109 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367109, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d367109, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367108 p = 1 := by simpa only [d367109, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44774 p hg
    simpa only [d367109, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44776 (p : Pattern) (guard : d367110 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367110, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d367110, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367109 p = 1 := by simpa only [d367110, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44775 p hg
    simpa only [d367110, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44777 (p : Pattern) (guard : d367111 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367100 p = 1 := by simpa only [d367111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44758 p hg
    simpa only [d367111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367110 p = 1 := by simpa only [d367111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44776 p hg
    simpa only [d367111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44778 (p : Pattern) (guard : d366899 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366867 p = 1 := by simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44732 p hg
    simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366891 p = 1 := by simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44746 p hg
    simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44779 (p : Pattern) (guard : d367112 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366899 p = 1 := by simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44778 p hg
    simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44780 (p : Pattern) (guard : d366900 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44781 (p : Pattern) (guard : d367113 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367112 p = 1 := by simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44779 p hg
    simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366900 p = 1 := by simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44780 p hg
    simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44782 (p : Pattern) (guard : d366901 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44783 (p : Pattern) (guard : d367114 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367113 p = 1 := by simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44781 p hg
    simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366901 p = 1 := by simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44782 p hg
    simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44784 (p : Pattern) (guard : d367115 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367114 p = 1 := by simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44783 p hg
    simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44785 (p : Pattern) (guard : d367116 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367115 p = 1 := by simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44784 p hg
    simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367095 p = 1 := by simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44786 (p : Pattern) (guard : d367117 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367116 p = 1 := by simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44785 p hg
    simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367106 p = 1 := by simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44772 p hg
    simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44787 (p : Pattern) (guard : d367118 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367097 p = 1 := by simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44755 p hg
    simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367117 p = 1 := by simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44786 p hg
    simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44788 (p : Pattern) (guard : d367119 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367118 p = 1 := by simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44787 p hg
    simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44789 (p : Pattern) (guard : d367120 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367119 p = 1 := by simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44788 p hg
    simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44790 (p : Pattern) (guard : d367121 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367106 p = 1 := by simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44772 p hg
    simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44791 (p : Pattern) (guard : d367122 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367117 p = 1 := by simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44786 p hg
    simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367121 p = 1 := by simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44790 p hg
    simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44792 (p : Pattern) (guard : d367123 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367122 p = 1 := by simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44791 p hg
    simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44793 (p : Pattern) (guard : d367124 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367123 p = 1 := by simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44792 p hg
    simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44794 (p : Pattern) (guard : d367125 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367120 p = 1 := by simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44789 p hg
    simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367124 p = 1 := by simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44793 p hg
    simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44795 (p : Pattern) (guard : d367126 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367111 p = 1 := by simpa only [d367126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44777 p hg
    simpa only [d367126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367125 p = 1 := by simpa only [d367126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44794 p hg
    simpa only [d367126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44796 (p : Pattern) (guard : d367127 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367126 p = 1 := by simpa only [d367127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44795 p hg
    simpa only [d367127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44797 (p : Pattern) (guard : d367128 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367127 p = 1 := by simpa only [d367128, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44796 p hg
    simpa only [d367128, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367128, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d367128, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44798 (p : Pattern) (guard : d367129 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367129, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367129, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367128 p = 1 := by simpa only [d367129, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44797 p hg
    simpa only [d367129, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44799 (p : Pattern) (guard : d367130 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367124 p = 1 := by simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44793 p hg
    simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44800 (p : Pattern) (guard : d367131 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367125 p = 1 := by simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44794 p hg
    simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367130 p = 1 := by simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44799 p hg
    simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44801 (p : Pattern) (guard : d367132 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367131 p = 1 := by simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44800 p hg
    simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44802 (p : Pattern) (guard : d367133 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367132 p = 1 := by simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44801 p hg
    simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44803 (p : Pattern) (guard : d367134 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367133 p = 1 := by simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44802 p hg
    simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44804 (p : Pattern) (guard : d367135 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367129 p = 1 := by simpa only [d367135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44798 p hg
    simpa only [d367135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367134 p = 1 := by simpa only [d367135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44803 p hg
    simpa only [d367135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44805 (p : Pattern) (guard : d367136 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367135 p = 1 := by simpa only [d367136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44804 p hg
    simpa only [d367136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44806 (p : Pattern) (guard : d367137 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367136 p = 1 := by simpa only [d367137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44805 p hg
    simpa only [d367137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44807 (p : Pattern) (guard : d367138 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367137 p = 1 := by simpa only [d367138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44806 p hg
    simpa only [d367138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44808 (p : Pattern) (guard : d367139 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367130 p = 1 := by simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44799 p hg
    simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44809 (p : Pattern) (guard : d367140 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367139 p = 1 := by simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44808 p hg
    simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44810 (p : Pattern) (guard : d367141 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367140 p = 1 := by simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44809 p hg
    simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44811 (p : Pattern) (guard : d367142 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367141 p = 1 := by simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44810 p hg
    simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44812 (p : Pattern) (guard : d367143 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367134 p = 1 := by simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44803 p hg
    simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367142 p = 1 := by simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44811 p hg
    simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44813 (p : Pattern) (guard : d367144 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367143 p = 1 := by simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44812 p hg
    simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44814 (p : Pattern) (guard : d367145 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367144 p = 1 := by simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44813 p hg
    simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44815 (p : Pattern) (guard : d367146 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367145 p = 1 := by simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44814 p hg
    simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44816 (p : Pattern) (guard : d367147 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367138 p = 1 := by simpa only [d367147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44807 p hg
    simpa only [d367147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367146 p = 1 := by simpa only [d367147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44815 p hg
    simpa only [d367147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44817 (p : Pattern) (guard : d367148 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367147 p = 1 := by simpa only [d367148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44816 p hg
    simpa only [d367148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44818 (p : Pattern) (guard : d367149 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367134 p = 1 := by simpa only [d367149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44803 p hg
    simpa only [d367149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44819 (p : Pattern) (guard : d367150 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367149 p = 1 := by simpa only [d367150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44818 p hg
    simpa only [d367150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44820 (p : Pattern) (guard : d367151 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367150 p = 1 := by simpa only [d367151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44819 p hg
    simpa only [d367151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44821 (p : Pattern) (guard : d367152 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367151 p = 1 := by simpa only [d367152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44820 p hg
    simpa only [d367152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44822 (p : Pattern) (guard : d367153 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367152 p = 1 := by simpa only [d367153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44821 p hg
    simpa only [d367153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44823 (p : Pattern) (guard : d367154 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367153 p = 1 := by simpa only [d367154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44822 p hg
    simpa only [d367154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44824 (p : Pattern) (guard : d367155 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367148 p = 1 := by simpa only [d367155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44817 p hg
    simpa only [d367155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367154 p = 1 := by simpa only [d367155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44823 p hg
    simpa only [d367155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44825 (p : Pattern) (guard : d367156 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367155 p = 1 := by simpa only [d367156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44824 p hg
    simpa only [d367156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44826 (p : Pattern) (guard : d367157 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367156 p = 1 := by simpa only [d367157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44825 p hg
    simpa only [d367157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44827 (p : Pattern) (guard : d367158 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367158, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367158, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367157 p = 1 := by simpa only [d367158, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44826 p hg
    simpa only [d367158, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44828 (p : Pattern) (guard : d367159 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367158 p = 1 := by simpa only [d367159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44827 p hg
    simpa only [d367159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44829 (p : Pattern) (guard : d367160 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367142 p = 1 := by simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44811 p hg
    simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44830 (p : Pattern) (guard : d367161 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367160 p = 1 := by simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44829 p hg
    simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44831 (p : Pattern) (guard : d367162 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367161 p = 1 := by simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44830 p hg
    simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44832 (p : Pattern) (guard : d367163 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367162 p = 1 := by simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44831 p hg
    simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44833 (p : Pattern) (guard : d367164 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367163 p = 1 := by simpa only [d367164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44832 p hg
    simpa only [d367164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44834 (p : Pattern) (guard : d367165 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367164 p = 1 := by simpa only [d367165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44833 p hg
    simpa only [d367165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44835 (p : Pattern) (guard : d367166 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367165 p = 1 := by simpa only [d367166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44834 p hg
    simpa only [d367166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44836 (p : Pattern) (guard : d367167 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367166 p = 1 := by simpa only [d367167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44835 p hg
    simpa only [d367167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44837 (p : Pattern) (guard : d367168 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367167 p = 1 := by simpa only [d367168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44836 p hg
    simpa only [d367168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44838 (p : Pattern) (guard : d367169 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367169, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367169, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367168 p = 1 := by simpa only [d367169, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44837 p hg
    simpa only [d367169, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44839 (p : Pattern) (guard : d367170 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367169 p = 1 := by simpa only [d367170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44838 p hg
    simpa only [d367170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44840 (p : Pattern) (guard : d367171 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367159 p = 1 := by simpa only [d367171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44828 p hg
    simpa only [d367171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367170 p = 1 := by simpa only [d367171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44839 p hg
    simpa only [d367171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44841 (p : Pattern) (guard : d367172 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367171 p = 1 := by simpa only [d367172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44840 p hg
    simpa only [d367172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44842 (p : Pattern) (guard : d367173 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367172 p = 1 := by simpa only [d367173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44841 p hg
    simpa only [d367173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44843 (p : Pattern) (guard : d367174 p = 1) : d51634 p ≤ (8 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367173 p = 1 := by simpa only [d367174, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44842 p hg
    simpa only [d367174, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367174, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d367174, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44844 (p : Pattern) (guard : d367175 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d367067 p = 1 := by simpa only [d367175, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44656 p hg
    simpa only [d367175, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367174 p = 1 := by simpa only [d367175, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44843 p hg
    simpa only [d367175, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44845 (p : Pattern) (guard : d367176 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367175 p = 1 := by simpa only [d367176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44844 p hg
    simpa only [d367176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44846 (p : Pattern) (guard : d367177 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367176 p = 1 := by simpa only [d367177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44845 p hg
    simpa only [d367177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44847 (p : Pattern) (guard : d367178 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367177 p = 1 := by simpa only [d367178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44846 p hg
    simpa only [d367178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44848 (p : Pattern) (guard : d367179 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367178 p = 1 := by simpa only [d367179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44847 p hg
    simpa only [d367179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44849 (p : Pattern) (guard : d367180 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367179 p = 1 := by simpa only [d367180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44848 p hg
    simpa only [d367180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44850 (p : Pattern) (guard : d367181 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367180 p = 1 := by simpa only [d367181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44849 p hg
    simpa only [d367181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44851 (p : Pattern) (guard : d367182 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367181 p = 1 := by simpa only [d367182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44850 p hg
    simpa only [d367182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44852 (p : Pattern) (guard : d367183 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367182 p = 1 := by simpa only [d367183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44851 p hg
    simpa only [d367183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44853 (p : Pattern) (guard : d367184 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367183 p = 1 := by simpa only [d367184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44852 p hg
    simpa only [d367184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44854 (p : Pattern) (guard : d367185 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d366853 p = 1 := by simpa only [d367185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44337 p hg
    simpa only [d367185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367184 p = 1 := by simpa only [d367185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44853 p hg
    simpa only [d367185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44855 (p : Pattern) (guard : d44446 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44856 (p : Pattern) (guard : d44447 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44446 p = 1 := by simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44855 p hg
    simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44857 (p : Pattern) (guard : d44448 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44447 p = 1 := by simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44856 p hg
    simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44858 (p : Pattern) (guard : d44449 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44448 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44857 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44859 (p : Pattern) (guard : d44611 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44860 (p : Pattern) (guard : d44612 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44611 p = 1 := by simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44859 p hg
    simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44861 (p : Pattern) (guard : d44613 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44612 p = 1 := by simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44860 p hg
    simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44862 (p : Pattern) (guard : d367186 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44448 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44857 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44613 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44861 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44863 (p : Pattern) (guard : d367187 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44449 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44858 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367186 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44862 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44864 (p : Pattern) (guard : d44614 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44613 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44861 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44865 (p : Pattern) (guard : d367188 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367186 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44862 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44614 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44864 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44866 (p : Pattern) (guard : d367189 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367187 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44863 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367188 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44865 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44867 (p : Pattern) (guard : d367190 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367189 p = 1 := by simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44866 p hg
    simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44868 (p : Pattern) (guard : d367191 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367190 p = 1 := by simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44867 p hg
    simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44869 (p : Pattern) (guard : d44616 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44614 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44864 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44870 (p : Pattern) (guard : d367192 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367188 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44865 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44616 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44869 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44871 (p : Pattern) (guard : d367193 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367192 p = 1 := by simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44870 p hg
    simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44872 (p : Pattern) (guard : d367194 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367193 p = 1 := by simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44871 p hg
    simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44873 (p : Pattern) (guard : d367195 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367191 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44868 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367194 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44872 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44874 (p : Pattern) (guard : d367196 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367194 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44872 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44875 (p : Pattern) (guard : d367197 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367195 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44873 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367196 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44874 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44876 (p : Pattern) (guard : d367198 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367197 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44875 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44877 (p : Pattern) (guard : d367199 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367198 p = 1 := by simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44876 p hg
    simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44878 (p : Pattern) (guard : d367200 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367199 p = 1 := by simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44877 p hg
    simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44879 (p : Pattern) (guard : d367201 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367196 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44874 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44880 (p : Pattern) (guard : d367202 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367201 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44879 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44881 (p : Pattern) (guard : d367203 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367202 p = 1 := by simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44880 p hg
    simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44882 (p : Pattern) (guard : d367204 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367203 p = 1 := by simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44881 p hg
    simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44883 (p : Pattern) (guard : d367205 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44878 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367204 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44882 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44884 (p : Pattern) (guard : d367206 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367205 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44883 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44885 (p : Pattern) (guard : d367207 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367206 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44884 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44886 (p : Pattern) (guard : d367208 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367207 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44885 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44887 (p : Pattern) (guard : d367209 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367204 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44882 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44888 (p : Pattern) (guard : d367210 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367209 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44887 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44889 (p : Pattern) (guard : d367211 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367210 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44888 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44890 (p : Pattern) (guard : d367212 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367211 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44889 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44891 (p : Pattern) (guard : d367213 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367208 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44886 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367212 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44890 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44892 (p : Pattern) (guard : d367214 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367213 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44891 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44893 (p : Pattern) (guard : d367215 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367214 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44892 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44894 (p : Pattern) (guard : d367216 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367215 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44893 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44895 (p : Pattern) (guard : d367217 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367216 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44894 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44896 (p : Pattern) (guard : d367218 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367217 p = 1 := by simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44895 p hg
    simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44897 (p : Pattern) (guard : d367219 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d367219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367218 p = 1 := by simpa only [d367219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44896 p hg
    simpa only [d367219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44898 (p : Pattern) (guard : d367220 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367219 p = 1 := by simpa only [d367220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44897 p hg
    simpa only [d367220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d367220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44899 (p : Pattern) (guard : d367200 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367199 p = 1 := by simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44877 p hg
    simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44900 (p : Pattern) (guard : d367204 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367203 p = 1 := by simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44881 p hg
    simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44901 (p : Pattern) (guard : d367205 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44899 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367204 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44900 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44902 (p : Pattern) (guard : d367206 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367205 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44901 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44903 (p : Pattern) (guard : d367207 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367206 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44902 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44904 (p : Pattern) (guard : d367208 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367207 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44903 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44905 (p : Pattern) (guard : d367209 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367204 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44900 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44906 (p : Pattern) (guard : d367210 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367209 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44905 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44907 (p : Pattern) (guard : d367211 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367210 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44906 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44908 (p : Pattern) (guard : d367212 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367211 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44907 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44909 (p : Pattern) (guard : d367213 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367208 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44904 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367212 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44908 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44910 (p : Pattern) (guard : d367214 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367213 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44909 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44911 (p : Pattern) (guard : d367215 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367214 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44910 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44912 (p : Pattern) (guard : d367216 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367215 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44911 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44913 (p : Pattern) (guard : d367217 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367216 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44912 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44914 (p : Pattern) (guard : d367221 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367207 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44885 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44915 (p : Pattern) (guard : d367222 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367211 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44889 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44916 (p : Pattern) (guard : d367223 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367221 p = 1 := by simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44914 p hg
    simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367222 p = 1 := by simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44915 p hg
    simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44917 (p : Pattern) (guard : d367224 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367223 p = 1 := by simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44916 p hg
    simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44918 (p : Pattern) (guard : d367225 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367224 p = 1 := by simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44917 p hg
    simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44919 (p : Pattern) (guard : d367226 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367225 p = 1 := by simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44918 p hg
    simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44920 (p : Pattern) (guard : d367227 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367226 p = 1 := by simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44921 (p : Pattern) (guard : d367228 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d367217 p = 1 := by simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44913 p hg
    simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367227 p = 1 := by simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44920 p hg
    simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44922 (p : Pattern) (guard : d367229 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d367218 p = 1 := by simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44896 p hg
    simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367228 p = 1 := by simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44921 p hg
    simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44923 (p : Pattern) (guard : d367230 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367229 p = 1 := by simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44922 p hg
    simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44924 (p : Pattern) (guard : d367231 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367220 p = 1 := by simpa only [d367231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44898 p hg
    simpa only [d367231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367230 p = 1 := by simpa only [d367231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44923 p hg
    simpa only [d367231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44925 (p : Pattern) (guard : d367232 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367206 p = 1 := by simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44884 p hg
    simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44926 (p : Pattern) (guard : d367233 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367232 p = 1 := by simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44927 (p : Pattern) (guard : d367234 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367210 p = 1 := by simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44888 p hg
    simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44928 (p : Pattern) (guard : d367235 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367234 p = 1 := by simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44927 p hg
    simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44929 (p : Pattern) (guard : d367236 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367233 p = 1 := by simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44926 p hg
    simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367235 p = 1 := by simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44928 p hg
    simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44930 (p : Pattern) (guard : d367237 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367236 p = 1 := by simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44929 p hg
    simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44931 (p : Pattern) (guard : d367238 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367237 p = 1 := by simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44930 p hg
    simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44932 (p : Pattern) (guard : d367239 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367238 p = 1 := by simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44931 p hg
    simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44933 (p : Pattern) (guard : d367240 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367205 p = 1 := by simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44883 p hg
    simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44934 (p : Pattern) (guard : d367241 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367240 p = 1 := by simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44933 p hg
    simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44935 (p : Pattern) (guard : d367242 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367241 p = 1 := by simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44934 p hg
    simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44936 (p : Pattern) (guard : d367243 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367209 p = 1 := by simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44887 p hg
    simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44937 (p : Pattern) (guard : d367244 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367243 p = 1 := by simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44936 p hg
    simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44938 (p : Pattern) (guard : d367245 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367244 p = 1 := by simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44937 p hg
    simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44939 (p : Pattern) (guard : d367246 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367242 p = 1 := by simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44935 p hg
    simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367245 p = 1 := by simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44938 p hg
    simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44940 (p : Pattern) (guard : d367247 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367246 p = 1 := by simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44939 p hg
    simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44941 (p : Pattern) (guard : d367248 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367247 p = 1 := by simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44940 p hg
    simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44942 (p : Pattern) (guard : d44535 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44449 p = 1 := by simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44858 p hg
    simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44943 (p : Pattern) (guard : d367249 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d44535 p = 1 := by simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44942 p hg
    simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367187 p = 1 := by simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44863 p hg
    simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44944 (p : Pattern) (guard : d367250 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367250, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d367250, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367249 p = 1 := by simpa only [d367250, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44943 p hg
    simpa only [d367250, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44945 (p : Pattern) (guard : d367251 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367251, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d367251, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367250 p = 1 := by simpa only [d367251, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44944 p hg
    simpa only [d367251, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44946 (p : Pattern) (guard : d367252 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367251 p = 1 := by simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44945 p hg
    simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367191 p = 1 := by simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44868 p hg
    simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44947 (p : Pattern) (guard : d367253 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367252 p = 1 := by simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44946 p hg
    simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367195 p = 1 := by simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44873 p hg
    simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44948 (p : Pattern) (guard : d367254 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367253 p = 1 := by simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44947 p hg
    simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44949 (p : Pattern) (guard : d367255 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367254 p = 1 := by simpa only [d367255, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44948 p hg
    simpa only [d367255, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367255, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d367255, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44950 (p : Pattern) (guard : d367256 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367256, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367256, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367255 p = 1 := by simpa only [d367256, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44949 p hg
    simpa only [d367256, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44951 (p : Pattern) (guard : d367257 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367256 p = 1 := by simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44950 p hg
    simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367200 p = 1 := by simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44878 p hg
    simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44952 (p : Pattern) (guard : d367258 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367257 p = 1 := by simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44951 p hg
    simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44953 (p : Pattern) (guard : d367259 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367258 p = 1 := by simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44952 p hg
    simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44954 (p : Pattern) (guard : d367260 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367259 p = 1 := by simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44953 p hg
    simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44955 (p : Pattern) (guard : d367261 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367260 p = 1 := by simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44954 p hg
    simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367208 p = 1 := by simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44886 p hg
    simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44956 (p : Pattern) (guard : d367262 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367261 p = 1 := by simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44955 p hg
    simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44957 (p : Pattern) (guard : d367263 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44878 p hg
    simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44958 (p : Pattern) (guard : d367264 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367263 p = 1 := by simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44957 p hg
    simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44959 (p : Pattern) (guard : d367265 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367264 p = 1 := by simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44958 p hg
    simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44960 (p : Pattern) (guard : d367266 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367265 p = 1 := by simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44959 p hg
    simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44961 (p : Pattern) (guard : d367267 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367266 p = 1 := by simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44960 p hg
    simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44962 (p : Pattern) (guard : d367268 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367267 p = 1 := by simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44961 p hg
    simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44963 (p : Pattern) (guard : d367269 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367262 p = 1 := by simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44956 p hg
    simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367268 p = 1 := by simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44962 p hg
    simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44964 (p : Pattern) (guard : d367270 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d367248 p = 1 := by simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44941 p hg
    simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367269 p = 1 := by simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44963 p hg
    simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44965 (p : Pattern) (guard : d367271 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d367239 p = 1 := by simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44932 p hg
    simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367270 p = 1 := by simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44964 p hg
    simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44966 (p : Pattern) (guard : d367272 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367272, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367272, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367271 p = 1 := by simpa only [d367272, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44965 p hg
    simpa only [d367272, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44967 (p : Pattern) (guard : d367232 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367206 p = 1 := by simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44902 p hg
    simpa only [d367232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44968 (p : Pattern) (guard : d367233 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367232 p = 1 := by simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d367233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44969 (p : Pattern) (guard : d367234 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367210 p = 1 := by simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44906 p hg
    simpa only [d367234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44970 (p : Pattern) (guard : d367235 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367234 p = 1 := by simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44969 p hg
    simpa only [d367235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44971 (p : Pattern) (guard : d367236 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367233 p = 1 := by simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44968 p hg
    simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367235 p = 1 := by simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44970 p hg
    simpa only [d367236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44972 (p : Pattern) (guard : d367237 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367236 p = 1 := by simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d367237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44973 (p : Pattern) (guard : d367238 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367237 p = 1 := by simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44972 p hg
    simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44974 (p : Pattern) (guard : d367239 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367238 p = 1 := by simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44973 p hg
    simpa only [d367239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44975 (p : Pattern) (guard : d367240 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367205 p = 1 := by simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44901 p hg
    simpa only [d367240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44976 (p : Pattern) (guard : d367241 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367240 p = 1 := by simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44975 p hg
    simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44977 (p : Pattern) (guard : d367242 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367241 p = 1 := by simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44976 p hg
    simpa only [d367242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44978 (p : Pattern) (guard : d367243 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367209 p = 1 := by simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44905 p hg
    simpa only [d367243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44979 (p : Pattern) (guard : d367244 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367243 p = 1 := by simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44978 p hg
    simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44980 (p : Pattern) (guard : d367245 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367244 p = 1 := by simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44979 p hg
    simpa only [d367245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44981 (p : Pattern) (guard : d367246 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367242 p = 1 := by simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44977 p hg
    simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367245 p = 1 := by simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44980 p hg
    simpa only [d367246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44982 (p : Pattern) (guard : d367247 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367246 p = 1 := by simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44981 p hg
    simpa only [d367247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44983 (p : Pattern) (guard : d367248 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367247 p = 1 := by simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44982 p hg
    simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44984 (p : Pattern) (guard : d367256 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367256, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d367256, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367255 p = 1 := by simpa only [d367256, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44949 p hg
    simpa only [d367256, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44985 (p : Pattern) (guard : d367257 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367256 p = 1 := by simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44984 p hg
    simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367200 p = 1 := by simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44899 p hg
    simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44986 (p : Pattern) (guard : d367258 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367257 p = 1 := by simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44985 p hg
    simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44987 (p : Pattern) (guard : d367259 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367258 p = 1 := by simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44986 p hg
    simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44988 (p : Pattern) (guard : d367260 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367259 p = 1 := by simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44987 p hg
    simpa only [d367260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44989 (p : Pattern) (guard : d367261 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367260 p = 1 := by simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44988 p hg
    simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367208 p = 1 := by simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44904 p hg
    simpa only [d367261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44990 (p : Pattern) (guard : d367262 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367261 p = 1 := by simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44989 p hg
    simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44991 (p : Pattern) (guard : d367263 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44899 p hg
    simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44992 (p : Pattern) (guard : d367264 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367263 p = 1 := by simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44991 p hg
    simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44993 (p : Pattern) (guard : d367265 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367264 p = 1 := by simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44992 p hg
    simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44994 (p : Pattern) (guard : d367266 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367265 p = 1 := by simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44993 p hg
    simpa only [d367266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44995 (p : Pattern) (guard : d367267 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367266 p = 1 := by simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44994 p hg
    simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44996 (p : Pattern) (guard : d367268 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367267 p = 1 := by simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44995 p hg
    simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44997 (p : Pattern) (guard : d367269 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367262 p = 1 := by simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44990 p hg
    simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367268 p = 1 := by simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44996 p hg
    simpa only [d367269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44998 (p : Pattern) (guard : d367270 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d367248 p = 1 := by simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44983 p hg
    simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367269 p = 1 := by simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44997 p hg
    simpa only [d367270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44999 (p : Pattern) (guard : d367271 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d367239 p = 1 := by simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44974 p hg
    simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367270 p = 1 := by simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44998 p hg
    simpa only [d367271, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
