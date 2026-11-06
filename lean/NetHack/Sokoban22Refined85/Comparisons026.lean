/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3640 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3641 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d4148, d21, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3642 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1178 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3639 p hg
    simpa only [d22, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d22, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3643 (p : Pattern) (guard : d4148 p = 1) : d28 p ≤ (0 : Int) + d1179 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d28, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d28, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d28, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d28, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3644 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1180 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3642 p hg
    simpa only [d29, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d29, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3645 (p : Pattern) (guard : d0 p = 1) : d78 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3646 (p : Pattern) (guard : d4148 p = 1) : d79 p ≤ (0 : Int) + d1181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d79, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d79, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d79, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3645 p hg
    simpa only [d4148, d79, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3647 (p : Pattern) (guard : d4148 p = 1) : d63 p ≤ (0 : Int) + d63 p := by
  omega
theorem compare3648 (p : Pattern) (guard : d4148 p = 1) : d80 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d80, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3646 p hg
    simpa only [d80, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d80, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d80, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3649 (p : Pattern) (guard : d4148 p = 1) : d81 p ≤ (0 : Int) + d1183 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d81, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3648 p hg
    simpa only [d81, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d81, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d81, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3650 (p : Pattern) (guard : d4148 p = 1) : d82 p ≤ (0 : Int) + d1184 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d82, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d82, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d82, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d82, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3651 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d1190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3652 (p : Pattern) (guard : d4303 p = 1) : d654 p ≤ (0 : Int) + d1191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d654, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3650 p hg
    simpa only [d4303, d654, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d654, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3651 p hg
    simpa only [d4303, d654, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3653 (p : Pattern) (guard : d4303 p = 1) : d655 p ≤ (0 : Int) + d1192 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d655, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3637 p hg
    simpa only [d655, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d655, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3652 p hg
    simpa only [d655, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3654 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d345 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3655 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1152 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3656 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3657 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d1193 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3656 p hg
    simpa only [d4148, d21, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3658 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1194 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d22, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d22, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3659 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1195 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3658 p hg
    simpa only [d29, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d29, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3660 (p : Pattern) (guard : d4148 p = 1) : d82 p ≤ (0 : Int) + d1196 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d82, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3659 p hg
    simpa only [d82, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d82, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d82, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3661 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1200 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3662 (p : Pattern) (guard : d4303 p = 1) : d656 p ≤ (0 : Int) + d1201 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d656, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3660 p hg
    simpa only [d4303, d656, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d656, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3661 p hg
    simpa only [d4303, d656, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3663 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (0 : Int) + d26 p := by
  omega
theorem compare3664 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3665 (p : Pattern) (guard : d4148 p = 1) : d89 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d89, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3663 p hg
    simpa only [d4148, d89, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d89, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d4148, d89, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3666 (p : Pattern) (guard : d4148 p = 1) : d90 p ≤ (0 : Int) + d1202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d90, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3665 p hg
    simpa only [d90, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d90, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d90, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3667 (p : Pattern) (guard : d4148 p = 1) : d91 p ≤ (0 : Int) + d91 p := by
  omega
theorem compare3668 (p : Pattern) (guard : d4148 p = 1) : d92 p ≤ (0 : Int) + d1203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d92, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3666 p hg
    simpa only [d92, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d92, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3667 p hg
    simpa only [d92, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3669 (p : Pattern) (guard : d4148 p = 1) : d93 p ≤ (0 : Int) + d93 p := by
  omega
theorem compare3670 (p : Pattern) (guard : d4148 p = 1) : d94 p ≤ (0 : Int) + d1204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d94, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3668 p hg
    simpa only [d94, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d94, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3669 p hg
    simpa only [d94, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3671 (p : Pattern) (guard : d4303 p = 1) : d657 p ≤ (0 : Int) + d1205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d657, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3670 p hg
    simpa only [d4303, d657, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d657, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d4303, d657, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3672 (p : Pattern) (guard : d4303 p = 1) : d658 p ≤ (0 : Int) + d1206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d658, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3662 p hg
    simpa only [d658, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d658, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3671 p hg
    simpa only [d658, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3673 (p : Pattern) (guard : d4303 p = 1) : d659 p ≤ (0 : Int) + d1207 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d659, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d659, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d659, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3672 p hg
    simpa only [d659, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3674 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d368 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3675 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1208 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3674 p hg
    simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3676 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3677 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d1185 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3676 p hg
    simpa only [d4148, d21, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3678 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1209 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3675 p hg
    simpa only [d22, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d22, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3679 (p : Pattern) (guard : d4148 p = 1) : d28 p ≤ (0 : Int) + d1210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d28, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d28, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d28, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d28, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3680 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1211 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3678 p hg
    simpa only [d29, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3679 p hg
    simpa only [d29, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3681 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3682 (p : Pattern) (guard : d4148 p = 1) : d38 p ≤ (0 : Int) + d1212 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d38, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d38, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d38, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3681 p hg
    simpa only [d4148, d38, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3683 (p : Pattern) (guard : d4148 p = 1) : d45 p ≤ (0 : Int) + d1213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d45, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3682 p hg
    simpa only [d45, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d45, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d45, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3684 (p : Pattern) (guard : d4148 p = 1) : d51 p ≤ (0 : Int) + d1214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d51, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3683 p hg
    simpa only [d51, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d51, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d51, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3685 (p : Pattern) (guard : d4148 p = 1) : d52 p ≤ (0 : Int) + d1215 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d52, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3680 p hg
    simpa only [d52, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d52, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3684 p hg
    simpa only [d52, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3686 (p : Pattern) (guard : d0 p = 1) : d397 p ≤ (0 : Int) + d1220 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3687 (p : Pattern) (guard : d4303 p = 1) : d660 p ≤ (0 : Int) + d1221 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d660, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3685 p hg
    simpa only [d4303, d660, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d660, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3686 p hg
    simpa only [d4303, d660, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3688 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3689 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1193 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3688 p hg
    simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3690 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1222 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d22, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d22, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3691 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1223 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3690 p hg
    simpa only [d29, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d29, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3692 (p : Pattern) (guard : d4148 p = 1) : d82 p ≤ (0 : Int) + d1224 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d82, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3691 p hg
    simpa only [d82, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d82, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d82, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3693 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1227 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3694 (p : Pattern) (guard : d4303 p = 1) : d661 p ≤ (0 : Int) + d1228 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d661, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3692 p hg
    simpa only [d4303, d661, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d661, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3693 p hg
    simpa only [d4303, d661, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3695 (p : Pattern) (guard : d4303 p = 1) : d662 p ≤ (0 : Int) + d1229 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d662, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3687 p hg
    simpa only [d662, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d662, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3694 p hg
    simpa only [d662, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3696 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3697 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1185 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3696 p hg
    simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3698 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1230 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3697 p hg
    simpa only [d22, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d22, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3699 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1231 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3698 p hg
    simpa only [d29, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d29, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3700 (p : Pattern) (guard : d4148 p = 1) : d82 p ≤ (0 : Int) + d1232 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d82, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d82, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d82, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d82, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3701 (p : Pattern) (guard : d0 p = 1) : d410 p ≤ (0 : Int) + d1227 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3702 (p : Pattern) (guard : d4303 p = 1) : d663 p ≤ (0 : Int) + d1233 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d663, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3700 p hg
    simpa only [d4303, d663, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d663, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3701 p hg
    simpa only [d4303, d663, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3703 (p : Pattern) (guard : d4303 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare3704 (p : Pattern) (guard : d4303 p = 1) : d664 p ≤ (0 : Int) + d1234 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d664, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d664, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d664, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d664, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3705 (p : Pattern) (guard : d4303 p = 1) : d665 p ≤ (0 : Int) + d1235 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d665, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3695 p hg
    simpa only [d665, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d665, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3704 p hg
    simpa only [d665, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3706 (p : Pattern) (guard : d4303 p = 1) : d666 p ≤ (0 : Int) + d1236 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d666, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3673 p hg
    simpa only [d666, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d666, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3705 p hg
    simpa only [d666, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3707 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3708 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3707 p hg
    simpa only [d4148, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3709 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1238 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3708 p hg
    simpa only [d22, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3619 p hg
    simpa only [d22, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3710 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3711 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d1197 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3710 p hg
    simpa only [d4148, d21, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3712 (p : Pattern) (guard : d4148 p = 1) : d28 p ≤ (0 : Int) + d1239 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d28, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3711 p hg
    simpa only [d28, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d28, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d28, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3713 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1240 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3709 p hg
    simpa only [d29, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3712 p hg
    simpa only [d29, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3714 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3715 (p : Pattern) (guard : d4148 p = 1) : d38 p ≤ (0 : Int) + d1241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d38, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d38, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d38, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3714 p hg
    simpa only [d4148, d38, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3716 (p : Pattern) (guard : d4148 p = 1) : d45 p ≤ (0 : Int) + d1242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d45, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3715 p hg
    simpa only [d45, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d45, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d45, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3717 (p : Pattern) (guard : d4148 p = 1) : d51 p ≤ (0 : Int) + d1243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d51, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3716 p hg
    simpa only [d51, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d51, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d51, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3718 (p : Pattern) (guard : d4148 p = 1) : d52 p ≤ (0 : Int) + d1244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d52, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3713 p hg
    simpa only [d52, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d52, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3717 p hg
    simpa only [d52, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3719 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d1248 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3720 (p : Pattern) (guard : d4303 p = 1) : d667 p ≤ (0 : Int) + d1249 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d667, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3718 p hg
    simpa only [d4303, d667, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d667, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3719 p hg
    simpa only [d4303, d667, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3721 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3722 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1197 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3723 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1250 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3722 p hg
    simpa only [d22, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d22, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3724 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3723 p hg
    simpa only [d29, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d29, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3725 (p : Pattern) (guard : d4148 p = 1) : d82 p ≤ (0 : Int) + d1252 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d82, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3724 p hg
    simpa only [d82, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d82, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d82, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3726 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d1255 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3727 (p : Pattern) (guard : d4303 p = 1) : d668 p ≤ (0 : Int) + d1256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d668, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3725 p hg
    simpa only [d4303, d668, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d668, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3726 p hg
    simpa only [d4303, d668, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3728 (p : Pattern) (guard : d4303 p = 1) : d669 p ≤ (0 : Int) + d1257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d669, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3720 p hg
    simpa only [d669, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d669, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3727 p hg
    simpa only [d669, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3729 (p : Pattern) (guard : d4303 p = 1) : d670 p ≤ (0 : Int) + d1205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d670, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3670 p hg
    simpa only [d4303, d670, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d670, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d4303, d670, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3730 (p : Pattern) (guard : d4303 p = 1) : d671 p ≤ (0 : Int) + d1258 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d671, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3652 p hg
    simpa only [d671, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d671, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3729 p hg
    simpa only [d671, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3731 (p : Pattern) (guard : d4303 p = 1) : d672 p ≤ (0 : Int) + d1259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d672, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3728 p hg
    simpa only [d672, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d672, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d672, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3732 (p : Pattern) (guard : d4148 p = 1) : d52 p ≤ (0 : Int) + d1260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d52, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3659 p hg
    simpa only [d52, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d52, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3684 p hg
    simpa only [d52, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3733 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1261 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3734 (p : Pattern) (guard : d4303 p = 1) : d673 p ≤ (0 : Int) + d1262 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d673, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3732 p hg
    simpa only [d4303, d673, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d673, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3733 p hg
    simpa only [d4303, d673, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3735 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3736 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3735 p hg
    simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3737 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3736 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3738 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1263 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d29, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d29, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3739 (p : Pattern) (guard : d4148 p = 1) : d82 p ≤ (0 : Int) + d1264 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3738 p hg
    simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3740 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1227 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3741 (p : Pattern) (guard : d4303 p = 1) : d674 p ≤ (0 : Int) + d1265 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d674, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d4303, d674, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d674, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3740 p hg
    simpa only [d4303, d674, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3742 (p : Pattern) (guard : d4303 p = 1) : d675 p ≤ (0 : Int) + d1266 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d675, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3734 p hg
    simpa only [d675, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d675, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3741 p hg
    simpa only [d675, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3743 (p : Pattern) (guard : d4303 p = 1) : d676 p ≤ (0 : Int) + d1267 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d676, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3694 p hg
    simpa only [d676, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d676, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d676, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3744 (p : Pattern) (guard : d4303 p = 1) : d677 p ≤ (0 : Int) + d1268 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d677, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d677, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d677, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3743 p hg
    simpa only [d677, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3745 (p : Pattern) (guard : d4303 p = 1) : d678 p ≤ (0 : Int) + d1269 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d678, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3731 p hg
    simpa only [d678, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d678, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d678, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3746 (p : Pattern) (guard : d4303 p = 1) : d679 p ≤ (0 : Int) + d1270 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d679, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d679, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d679, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3745 p hg
    simpa only [d679, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3747 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3748 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d1271 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3747 p hg
    simpa only [d4148, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3749 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d354 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3750 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (0 : Int) + d1272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d110, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3749 p hg
    simpa only [d4148, d110, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3751 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d1273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3748 p hg
    simpa only [d111, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3750 p hg
    simpa only [d111, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3752 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3753 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (0 : Int) + d1274 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d110, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3752 p hg
    simpa only [d4148, d110, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3754 (p : Pattern) (guard : d4148 p = 1) : d112 p ≤ (0 : Int) + d112 p := by
  omega
theorem compare3755 (p : Pattern) (guard : d4148 p = 1) : d113 p ≤ (0 : Int) + d1275 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d113, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3753 p hg
    simpa only [d113, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d113, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d113, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3756 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1276 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d114, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3755 p hg
    simpa only [d114, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3757 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (0 : Int) + d118 p := by
  omega
theorem compare3758 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3759 (p : Pattern) (guard : d4148 p = 1) : d123 p ≤ (0 : Int) + d1277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d123, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d123, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d123, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3758 p hg
    simpa only [d4148, d123, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3760 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (0 : Int) + d124 p := by
  omega
theorem compare3761 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3762 (p : Pattern) (guard : d4148 p = 1) : d126 p ≤ (0 : Int) + d1278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d126, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3760 p hg
    simpa only [d4148, d126, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d126, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d4148, d126, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3763 (p : Pattern) (guard : d4148 p = 1) : d127 p ≤ (0 : Int) + d1279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d127, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3759 p hg
    simpa only [d127, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d127, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d127, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3764 (p : Pattern) (guard : d4148 p = 1) : d128 p ≤ (0 : Int) + d128 p := by
  omega
theorem compare3765 (p : Pattern) (guard : d4148 p = 1) : d129 p ≤ (0 : Int) + d1280 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d129, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d129, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d129, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d129, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3766 (p : Pattern) (guard : d4148 p = 1) : d130 p ≤ (0 : Int) + d1281 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d130, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3763 p hg
    simpa only [d130, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d130, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3765 p hg
    simpa only [d130, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3767 (p : Pattern) (guard : d4148 p = 1) : d131 p ≤ (0 : Int) + d1282 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d131, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3756 p hg
    simpa only [d131, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d131, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3766 p hg
    simpa only [d131, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3768 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d1294 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3769 (p : Pattern) (guard : d4303 p = 1) : d680 p ≤ (0 : Int) + d1295 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d680, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3767 p hg
    simpa only [d4303, d680, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d680, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3768 p hg
    simpa only [d4303, d680, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3770 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3771 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d1274 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3770 p hg
    simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3772 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3773 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (0 : Int) + d1296 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d110, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d4148, d110, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3774 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d1297 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3771 p hg
    simpa only [d111, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d111, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3775 (p : Pattern) (guard : d4148 p = 1) : d113 p ≤ (0 : Int) + d1298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d113, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d113, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d113, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d113, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3776 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1299 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3774 p hg
    simpa only [d114, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d114, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3777 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3778 (p : Pattern) (guard : d4148 p = 1) : d149 p ≤ (0 : Int) + d1289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d149, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d149, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d149, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3777 p hg
    simpa only [d4148, d149, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3779 (p : Pattern) (guard : d4148 p = 1) : d150 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d150, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3778 p hg
    simpa only [d150, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d150, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d150, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
