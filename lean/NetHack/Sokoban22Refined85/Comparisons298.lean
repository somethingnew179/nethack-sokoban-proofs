/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons297
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41720 (p : Pattern) (guard : d8136 p = 1) : d605 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d605, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41718 p hg
    simpa only [d8136, d605, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d605, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41719 p hg
    simpa only [d8136, d605, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41721 (p : Pattern) (guard : d8142 p = 1) : d606 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d606, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41720 p hg
    simpa only [d8142, d606, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d606, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d606, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41722 (p : Pattern) (guard : d8143 p = 1) : d607 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d607, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41710 p hg
    simpa only [d8143, d607, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d607, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41721 p hg
    simpa only [d8143, d607, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41723 (p : Pattern) (guard : d8144 p = 1) : d608 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d608, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41709 p hg
    simpa only [d8144, d608, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d608, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41722 p hg
    simpa only [d8144, d608, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41724 (p : Pattern) (guard : d8145 p = 1) : d609 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d609, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41656 p hg
    simpa only [d8145, d609, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d609, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41723 p hg
    simpa only [d8145, d609, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41725 (p : Pattern) (guard : d8131 p = 1) : d400 p ≤ (0 : Int) + d400 p := by
  omega
theorem compare41726 (p : Pattern) (guard : d8132 p = 1) : d517 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35615 p hg
    simpa only [d8132, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41725 p hg
    simpa only [d8132, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41727 (p : Pattern) (guard : d8100 p = 1) : d518 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35071 p hg
    simpa only [d8100, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41728 (p : Pattern) (guard : d8106 p = 1) : d519 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41727 p hg
    simpa only [d8106, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41729 (p : Pattern) (guard : d8112 p = 1) : d521 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41728 p hg
    simpa only [d8112, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41616 p hg
    simpa only [d8112, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41730 (p : Pattern) (guard : d8118 p = 1) : d526 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41729 p hg
    simpa only [d8118, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41620 p hg
    simpa only [d8118, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41731 (p : Pattern) (guard : d8124 p = 1) : d530 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41730 p hg
    simpa only [d8124, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41622 p hg
    simpa only [d8124, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41732 (p : Pattern) (guard : d8125 p = 1) : d531 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35496 p hg
    simpa only [d8125, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41731 p hg
    simpa only [d8125, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41733 (p : Pattern) (guard : d8130 p = 1) : d542 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35531 p hg
    simpa only [d8130, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41630 p hg
    simpa only [d8130, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41734 (p : Pattern) (guard : d8131 p = 1) : d543 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41732 p hg
    simpa only [d8131, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41733 p hg
    simpa only [d8131, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41735 (p : Pattern) (guard : d8137 p = 1) : d544 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41734 p hg
    simpa only [d8137, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41682 p hg
    simpa only [d8137, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41736 (p : Pattern) (guard : d8138 p = 1) : d545 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41726 p hg
    simpa only [d8138, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41735 p hg
    simpa only [d8138, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41737 (p : Pattern) (guard : d8136 p = 1) : d422 p ≤ (0 : Int) + d422 p := by
  omega
theorem compare41738 (p : Pattern) (guard : d8137 p = 1) : d546 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35677 p hg
    simpa only [d8137, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41737 p hg
    simpa only [d8137, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41739 (p : Pattern) (guard : d0 p = 1) : d525 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41740 (p : Pattern) (guard : d8123 p = 1) : d526 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41713 p hg
    simpa only [d8123, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41739 p hg
    simpa only [d8123, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41741 (p : Pattern) (guard : d0 p = 1) : d529 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41742 (p : Pattern) (guard : d8129 p = 1) : d530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41740 p hg
    simpa only [d8129, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41741 p hg
    simpa only [d8129, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41743 (p : Pattern) (guard : d8130 p = 1) : d531 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38280 p hg
    simpa only [d8130, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41742 p hg
    simpa only [d8130, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41744 (p : Pattern) (guard : d8135 p = 1) : d542 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41500 p hg
    simpa only [d8135, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d8135, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41745 (p : Pattern) (guard : d8136 p = 1) : d543 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41743 p hg
    simpa only [d8136, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41744 p hg
    simpa only [d8136, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41746 (p : Pattern) (guard : d8142 p = 1) : d547 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41745 p hg
    simpa only [d8142, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41747 (p : Pattern) (guard : d8143 p = 1) : d548 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41738 p hg
    simpa only [d8143, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41746 p hg
    simpa only [d8143, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41748 (p : Pattern) (guard : d8144 p = 1) : d549 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41736 p hg
    simpa only [d8144, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41747 p hg
    simpa only [d8144, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41749 (p : Pattern) (guard : d8136 p = 1) : d457 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d457, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38223 p hg
    simpa only [d8136, d457, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d457, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35858 p hg
    simpa only [d8136, d457, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41750 (p : Pattern) (guard : d8137 p = 1) : d610 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d610, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35782 p hg
    simpa only [d8137, d610, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d610, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41749 p hg
    simpa only [d8137, d610, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41751 (p : Pattern) (guard : d8105 p = 1) : d558 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35368 p hg
    simpa only [d8105, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41752 (p : Pattern) (guard : d8111 p = 1) : d559 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41751 p hg
    simpa only [d8111, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d8111, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41753 (p : Pattern) (guard : d8117 p = 1) : d561 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41752 p hg
    simpa only [d8117, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41685 p hg
    simpa only [d8117, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41754 (p : Pattern) (guard : d8123 p = 1) : d566 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41753 p hg
    simpa only [d8123, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41687 p hg
    simpa only [d8123, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41755 (p : Pattern) (guard : d8129 p = 1) : d568 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41754 p hg
    simpa only [d8129, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41689 p hg
    simpa only [d8129, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41756 (p : Pattern) (guard : d8130 p = 1) : d569 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38298 p hg
    simpa only [d8130, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41755 p hg
    simpa only [d8130, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41757 (p : Pattern) (guard : d8135 p = 1) : d615 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d615, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41509 p hg
    simpa only [d8135, d615, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d615, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2882 p hg
    simpa only [d8135, d615, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41758 (p : Pattern) (guard : d8136 p = 1) : d616 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d616, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41756 p hg
    simpa only [d8136, d616, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d616, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41757 p hg
    simpa only [d8136, d616, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41759 (p : Pattern) (guard : d8142 p = 1) : d617 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d617, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41758 p hg
    simpa only [d8142, d617, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d617, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35812 p hg
    simpa only [d8142, d617, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41760 (p : Pattern) (guard : d8143 p = 1) : d618 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d618, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41750 p hg
    simpa only [d8143, d618, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d618, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41759 p hg
    simpa only [d8143, d618, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41761 (p : Pattern) (guard : d8141 p = 1) : d473 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d473, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38282 p hg
    simpa only [d8141, d473, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d473, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38319 p hg
    simpa only [d8141, d473, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41762 (p : Pattern) (guard : d8142 p = 1) : d619 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d619, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35845 p hg
    simpa only [d8142, d619, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d619, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41761 p hg
    simpa only [d8142, d619, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41763 (p : Pattern) (guard : d8135 p = 1) : d631 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d631, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41530 p hg
    simpa only [d8135, d631, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d631, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d8135, d631, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41764 (p : Pattern) (guard : d0 p = 1) : d645 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41765 (p : Pattern) (guard : d8141 p = 1) : d646 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d646, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41763 p hg
    simpa only [d8141, d646, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d646, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41764 p hg
    simpa only [d8141, d646, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41766 (p : Pattern) (guard : d8147 p = 1) : d647 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d647, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41765 p hg
    simpa only [d8147, d647, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d647, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d647, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41767 (p : Pattern) (guard : d8148 p = 1) : d648 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d648, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41762 p hg
    simpa only [d8148, d648, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d648, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41766 p hg
    simpa only [d8148, d648, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41768 (p : Pattern) (guard : d8149 p = 1) : d649 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d649, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41760 p hg
    simpa only [d8149, d649, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d649, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41767 p hg
    simpa only [d8149, d649, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41769 (p : Pattern) (guard : d8150 p = 1) : d650 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d650, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41748 p hg
    simpa only [d8150, d650, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d650, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41768 p hg
    simpa only [d8150, d650, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41770 (p : Pattern) (guard : d8151 p = 1) : d651 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41724 p hg
    simpa only [d8151, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41769 p hg
    simpa only [d8151, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41771 (p : Pattern) (guard : d8152 p = 1) : d652 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41698 p hg
    simpa only [d8152, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41770 p hg
    simpa only [d8152, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41772 (p : Pattern) (guard : d1 p = 1) : d2503 p ≤ (0 : Int) + d316 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2503, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34318 p hg
    simpa only [d2503, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2503, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17514 p hg
    simpa only [d2503, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41773 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34321 p hg
    simpa only [d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41774 (p : Pattern) (guard : d1 p = 1) : d2505 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41772 p hg
    simpa only [d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41773 p hg
    simpa only [d2505, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41775 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41776 (p : Pattern) (guard : d1 p = 1) : d2506 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41777 (p : Pattern) (guard : d1 p = 1) : d2507 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41775 p hg
    simpa only [d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41776 p hg
    simpa only [d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41778 (p : Pattern) (guard : d1 p = 1) : d2508 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41774 p hg
    simpa only [d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41777 p hg
    simpa only [d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41779 (p : Pattern) (guard : d1 p = 1) : d2509 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41780 (p : Pattern) (guard : d1 p = 1) : d2510 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41773 p hg
    simpa only [d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41779 p hg
    simpa only [d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41781 (p : Pattern) (guard : d8087 p = 1) : d2511 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41780 p hg
    simpa only [d8087, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41782 (p : Pattern) (guard : d8088 p = 1) : d2512 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41778 p hg
    simpa only [d8088, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41781 p hg
    simpa only [d8088, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41783 (p : Pattern) (guard : d1 p = 1) : d2513 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34331 p hg
    simpa only [d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17141 p hg
    simpa only [d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41784 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41785 (p : Pattern) (guard : d1 p = 1) : d2514 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41783 p hg
    simpa only [d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41784 p hg
    simpa only [d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41786 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41787 (p : Pattern) (guard : d8084 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare41788 (p : Pattern) (guard : d8085 p = 1) : d2506 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d8085, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41789 (p : Pattern) (guard : d8086 p = 1) : d2507 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41786 p hg
    simpa only [d8086, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41788 p hg
    simpa only [d8086, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41790 (p : Pattern) (guard : d8087 p = 1) : d2515 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41785 p hg
    simpa only [d8087, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41789 p hg
    simpa only [d8087, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41791 (p : Pattern) (guard : d8085 p = 1) : d2509 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d8085, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41792 (p : Pattern) (guard : d8086 p = 1) : d2510 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41784 p hg
    simpa only [d8086, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41791 p hg
    simpa only [d8086, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41793 (p : Pattern) (guard : d8091 p = 1) : d2511 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41792 p hg
    simpa only [d8091, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41794 (p : Pattern) (guard : d8092 p = 1) : d2516 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41790 p hg
    simpa only [d8092, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41793 p hg
    simpa only [d8092, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41795 (p : Pattern) (guard : d8093 p = 1) : d2517 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41782 p hg
    simpa only [d8093, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41794 p hg
    simpa only [d8093, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41796 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34348 p hg
    simpa only [d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41797 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41796 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41786 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41798 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41799 (p : Pattern) (guard : d8086 p = 1) : d2507 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41798 p hg
    simpa only [d8086, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41788 p hg
    simpa only [d8086, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41800 (p : Pattern) (guard : d8087 p = 1) : d2518 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41797 p hg
    simpa only [d8087, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41799 p hg
    simpa only [d8087, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41801 (p : Pattern) (guard : d8086 p = 1) : d2510 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41786 p hg
    simpa only [d8086, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41791 p hg
    simpa only [d8086, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41802 (p : Pattern) (guard : d8091 p = 1) : d2511 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41801 p hg
    simpa only [d8091, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41803 (p : Pattern) (guard : d8092 p = 1) : d2519 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41800 p hg
    simpa only [d8092, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41802 p hg
    simpa only [d8092, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41804 (p : Pattern) (guard : d1 p = 1) : d2520 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34356 p hg
    simpa only [d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41805 (p : Pattern) (guard : d8085 p = 1) : d2520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d8085, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41806 (p : Pattern) (guard : d8086 p = 1) : d2520 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41804 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41805 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41807 (p : Pattern) (guard : d1 p = 1) : d1794 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41808 (p : Pattern) (guard : d8084 p = 1) : d1795 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41807 p hg
    simpa only [d8084, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35917 p hg
    simpa only [d8084, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41809 (p : Pattern) (guard : d8089 p = 1) : d2521 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41808 p hg
    simpa only [d8089, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41810 (p : Pattern) (guard : d8090 p = 1) : d2522 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41805 p hg
    simpa only [d8090, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41809 p hg
    simpa only [d8090, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41811 (p : Pattern) (guard : d8091 p = 1) : d2523 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41806 p hg
    simpa only [d8091, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41810 p hg
    simpa only [d8091, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41812 (p : Pattern) (guard : d8089 p = 1) : d2524 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38358 p hg
    simpa only [d8089, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41813 (p : Pattern) (guard : d8090 p = 1) : d2525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41805 p hg
    simpa only [d8090, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41812 p hg
    simpa only [d8090, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41814 (p : Pattern) (guard : d8095 p = 1) : d2526 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41813 p hg
    simpa only [d8095, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41815 (p : Pattern) (guard : d8096 p = 1) : d2527 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41811 p hg
    simpa only [d8096, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41814 p hg
    simpa only [d8096, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41816 (p : Pattern) (guard : d8097 p = 1) : d2528 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41803 p hg
    simpa only [d8097, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41815 p hg
    simpa only [d8097, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41817 (p : Pattern) (guard : d8098 p = 1) : d2529 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41795 p hg
    simpa only [d8098, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41816 p hg
    simpa only [d8098, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41818 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34372 p hg
    simpa only [d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41819 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41818 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41798 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41820 (p : Pattern) (guard : d8087 p = 1) : d2518 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41819 p hg
    simpa only [d8087, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41799 p hg
    simpa only [d8087, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41821 (p : Pattern) (guard : d8086 p = 1) : d2510 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41798 p hg
    simpa only [d8086, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41791 p hg
    simpa only [d8086, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41822 (p : Pattern) (guard : d8091 p = 1) : d2511 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41821 p hg
    simpa only [d8091, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41823 (p : Pattern) (guard : d8092 p = 1) : d2519 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41820 p hg
    simpa only [d8092, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41822 p hg
    simpa only [d8092, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41824 (p : Pattern) (guard : d1 p = 1) : d2520 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34380 p hg
    simpa only [d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41825 (p : Pattern) (guard : d8086 p = 1) : d2520 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41824 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41805 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41826 (p : Pattern) (guard : d8091 p = 1) : d2523 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41825 p hg
    simpa only [d8091, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41810 p hg
    simpa only [d8091, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41827 (p : Pattern) (guard : d8096 p = 1) : d2527 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41826 p hg
    simpa only [d8096, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41814 p hg
    simpa only [d8096, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41828 (p : Pattern) (guard : d8097 p = 1) : d2528 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41823 p hg
    simpa only [d8097, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41827 p hg
    simpa only [d8097, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41829 (p : Pattern) (guard : d1 p = 1) : d2530 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34386 p hg
    simpa only [d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41830 (p : Pattern) (guard : d8085 p = 1) : d2530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d8085, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41831 (p : Pattern) (guard : d8086 p = 1) : d2530 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41829 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41830 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41832 (p : Pattern) (guard : d8089 p = 1) : d357 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35954 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41833 (p : Pattern) (guard : d8090 p = 1) : d2531 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41830 p hg
    simpa only [d8090, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41832 p hg
    simpa only [d8090, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41834 (p : Pattern) (guard : d8091 p = 1) : d2532 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41831 p hg
    simpa only [d8091, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41833 p hg
    simpa only [d8091, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41835 (p : Pattern) (guard : d8089 p = 1) : d2533 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38378 p hg
    simpa only [d8089, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41836 (p : Pattern) (guard : d8090 p = 1) : d2534 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41830 p hg
    simpa only [d8090, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41835 p hg
    simpa only [d8090, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41837 (p : Pattern) (guard : d8095 p = 1) : d2535 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41836 p hg
    simpa only [d8095, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41838 (p : Pattern) (guard : d8096 p = 1) : d2536 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41834 p hg
    simpa only [d8096, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41837 p hg
    simpa only [d8096, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41839 (p : Pattern) (guard : d8102 p = 1) : d2537 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41838 p hg
    simpa only [d8102, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41840 (p : Pattern) (guard : d8103 p = 1) : d2538 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41828 p hg
    simpa only [d8103, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41839 p hg
    simpa only [d8103, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41841 (p : Pattern) (guard : d8104 p = 1) : d2539 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41817 p hg
    simpa only [d8104, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41840 p hg
    simpa only [d8104, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41842 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34403 p hg
    simpa only [d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41843 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41842 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41798 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41844 (p : Pattern) (guard : d8087 p = 1) : d2518 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41843 p hg
    simpa only [d8087, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41799 p hg
    simpa only [d8087, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41845 (p : Pattern) (guard : d1 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41846 (p : Pattern) (guard : d8085 p = 1) : d2541 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38394 p hg
    simpa only [d8085, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41847 (p : Pattern) (guard : d8086 p = 1) : d2542 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41845 p hg
    simpa only [d8086, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41846 p hg
    simpa only [d8086, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41848 (p : Pattern) (guard : d8091 p = 1) : d2543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41847 p hg
    simpa only [d8091, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41849 (p : Pattern) (guard : d8092 p = 1) : d2544 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41844 p hg
    simpa only [d8092, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41848 p hg
    simpa only [d8092, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41850 (p : Pattern) (guard : d1 p = 1) : d2504 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41851 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d8085, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41852 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41850 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41853 (p : Pattern) (guard : d8089 p = 1) : d2506 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8089, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41854 (p : Pattern) (guard : d8090 p = 1) : d2507 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8090, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41853 p hg
    simpa only [d8090, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41855 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41852 p hg
    simpa only [d8091, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41856 (p : Pattern) (guard : d8085 p = 1) : d2545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d8085, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41857 (p : Pattern) (guard : d8089 p = 1) : d2546 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38401 p hg
    simpa only [d8089, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41858 (p : Pattern) (guard : d8090 p = 1) : d2547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41856 p hg
    simpa only [d8090, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41857 p hg
    simpa only [d8090, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41859 (p : Pattern) (guard : d8095 p = 1) : d2548 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41858 p hg
    simpa only [d8095, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
