/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalComparisons00
import NetHack.Sokoban41.Comparisons35
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem goalC160 (pattern : Ten) (guard : d790 pattern = 1) : d125 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d125, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC158 pattern childGuard
    simpa only [d790, d125, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d125, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC159 pattern childGuard
    simpa only [d790, d125, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC161 (pattern : Ten) (guard : d608 pattern = 1) : d48 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC45 pattern childGuard
    simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c826 pattern childGuard
    simpa only [d608, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC162 (pattern : Ten) (guard : d609 pattern = 1) : d48 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC161 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c826 pattern childGuard
    simpa only [d609, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC163 (pattern : Ten) (guard : d791 pattern = 1) : d128 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d128, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC160 pattern childGuard
    simpa only [d791, d128, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d128, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC162 pattern childGuard
    simpa only [d791, d128, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC164 (pattern : Ten) (guard : d608 pattern = 1) : d48 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC50 pattern childGuard
    simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c826 pattern childGuard
    simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC165 (pattern : Ten) (guard : d609 pattern = 1) : d126 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d126, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC164 pattern childGuard
    simpa only [d609, d126, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d126, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d609, d126, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC166 (pattern : Ten) (guard : d0 pattern = 1) : d127 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC167 (pattern : Ten) (guard : d610 pattern = 1) : d129 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d129, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC165 pattern childGuard
    simpa only [d610, d129, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d129, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC166 pattern childGuard
    simpa only [d610, d129, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC168 (pattern : Ten) (guard : d792 pattern = 1) : d130 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d130, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC163 pattern childGuard
    simpa only [d792, d130, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d130, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC167 pattern childGuard
    simpa only [d792, d130, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC169 (pattern : Ten) (guard : d609 pattern = 1) : d126 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d126, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC161 pattern childGuard
    simpa only [d609, d126, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d126, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d609, d126, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC170 (pattern : Ten) (guard : d610 pattern = 1) : d129 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d129, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC169 pattern childGuard
    simpa only [d610, d129, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d129, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC166 pattern childGuard
    simpa only [d610, d129, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC171 (pattern : Ten) (guard : d611 pattern = 1) : d131 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d131, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC170 pattern childGuard
    simpa only [d611, d131, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d131, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d611, d131, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC172 (pattern : Ten) (guard : d793 pattern = 1) : d132 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d132, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC168 pattern childGuard
    simpa only [d793, d132, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d132, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC171 pattern childGuard
    simpa only [d793, d132, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC173 (pattern : Ten) (guard : d610 pattern = 1) : d7 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC87 pattern childGuard
    simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d610, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC174 (pattern : Ten) (guard : d611 pattern = 1) : d7 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC175 (pattern : Ten) (guard : d793 pattern = 1) : d133 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d133, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC55 pattern childGuard
    simpa only [d793, d133, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d133, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC174 pattern childGuard
    simpa only [d793, d133, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC176 (pattern : Ten) (guard : d359 pattern = 1) : d8 pattern ≤ (0 : Int) + d8 pattern := by
  omega
theorem goalC177 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC178 (pattern : Ten) (guard : d606 pattern = 1) : d8 pattern ≤ (0 : Int) + d45 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC176 pattern childGuard
    simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC177 pattern childGuard
    simpa only [d606, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC179 (pattern : Ten) (guard : d607 pattern = 1) : d8 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC178 pattern childGuard
    simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC177 pattern childGuard
    simpa only [d607, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC180 (pattern : Ten) (guard : d608 pattern = 1) : d8 pattern ≤ (0 : Int) + d810 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC179 pattern childGuard
    simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC177 pattern childGuard
    simpa only [d608, d810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC181 (pattern : Ten) (guard : d609 pattern = 1) : d8 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC180 pattern childGuard
    simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC177 pattern childGuard
    simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC182 (pattern : Ten) (guard : d610 pattern = 1) : d8 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC181 pattern childGuard
    simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC177 pattern childGuard
    simpa only [d610, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC183 (pattern : Ten) (guard : d792 pattern = 1) : d134 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d134, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC48 pattern childGuard
    simpa only [d792, d134, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d134, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC182 pattern childGuard
    simpa only [d792, d134, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC184 (pattern : Ten) (guard : d611 pattern = 1) : d56 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC60 pattern childGuard
    simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1152 pattern childGuard
    simpa only [d611, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC185 (pattern : Ten) (guard : d793 pattern = 1) : d135 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d135, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC183 pattern childGuard
    simpa only [d793, d135, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d135, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d793, d135, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC186 (pattern : Ten) (guard : d787 pattern = 1) : d138 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d786 pattern = 1 := by simpa only [d787, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC0 pattern childGuard
    simpa only [d787, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d787, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5444 pattern childGuard
    simpa only [d787, d138, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC187 (pattern : Ten) (guard : d788 pattern = 1) : d139 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d787 pattern = 1 := by simpa only [d788, d139, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC186 pattern childGuard
    simpa only [d788, d139, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d788, d139, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC3 pattern childGuard
    simpa only [d788, d139, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC188 (pattern : Ten) (guard : d789 pattern = 1) : d142 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d788 pattern = 1 := by simpa only [d789, d142, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC187 pattern childGuard
    simpa only [d789, d142, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d789, d142, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC6 pattern childGuard
    simpa only [d789, d142, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC189 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d12, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d606, d12, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC190 (pattern : Ten) (guard : d607 pattern = 1) : d140 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d140, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC189 pattern childGuard
    simpa only [d607, d140, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d140, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d607, d140, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC191 (pattern : Ten) (guard : d608 pattern = 1) : d143 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d143, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC190 pattern childGuard
    simpa only [d608, d143, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d143, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d608, d143, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC192 (pattern : Ten) (guard : d790 pattern = 1) : d145 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d145, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC188 pattern childGuard
    simpa only [d790, d145, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d145, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC191 pattern childGuard
    simpa only [d790, d145, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC193 (pattern : Ten) (guard : d607 pattern = 1) : d141 pattern ≤ (0 : Int) + d806 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d141, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC27 pattern childGuard
    simpa only [d607, d141, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d141, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC13 pattern childGuard
    simpa only [d607, d141, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC194 (pattern : Ten) (guard : d608 pattern = 1) : d144 pattern ≤ (0 : Int) + d807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d144, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC193 pattern childGuard
    simpa only [d608, d144, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d144, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC15 pattern childGuard
    simpa only [d608, d144, d807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC195 (pattern : Ten) (guard : d0 pattern = 1) : d143 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC196 (pattern : Ten) (guard : d609 pattern = 1) : d146 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d146, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC194 pattern childGuard
    simpa only [d609, d146, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d146, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC195 pattern childGuard
    simpa only [d609, d146, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC197 (pattern : Ten) (guard : d791 pattern = 1) : d147 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d147, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC192 pattern childGuard
    simpa only [d791, d147, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d147, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC196 pattern childGuard
    simpa only [d791, d147, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC198 (pattern : Ten) (guard : d792 pattern = 1) : d148 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d148, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC197 pattern childGuard
    simpa only [d792, d148, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d148, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC25 pattern childGuard
    simpa only [d792, d148, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC199 (pattern : Ten) (guard : d793 pattern = 1) : d149 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d149, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC198 pattern childGuard
    simpa only [d793, d149, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d149, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC32 pattern childGuard
    simpa only [d793, d149, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC200 (pattern : Ten) (guard : d359 pattern = 1) : d9 pattern ≤ (0 : Int) + d9 pattern := by
  omega
theorem goalC201 (pattern : Ten) (guard : d606 pattern = 1) : d9 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC200 pattern childGuard
    simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c109 pattern childGuard
    simpa only [d606, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC202 (pattern : Ten) (guard : d607 pattern = 1) : d9 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC201 pattern childGuard
    simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c109 pattern childGuard
    simpa only [d607, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC203 (pattern : Ten) (guard : d608 pattern = 1) : d9 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC202 pattern childGuard
    simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c109 pattern childGuard
    simpa only [d608, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC204 (pattern : Ten) (guard : d790 pattern = 1) : d150 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d150, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC38 pattern childGuard
    simpa only [d790, d150, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d150, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC203 pattern childGuard
    simpa only [d790, d150, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC205 (pattern : Ten) (guard : d791 pattern = 1) : d151 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d151, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC204 pattern childGuard
    simpa only [d791, d151, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d151, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC47 pattern childGuard
    simpa only [d791, d151, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC206 (pattern : Ten) (guard : d609 pattern = 1) : d54 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC51 pattern childGuard
    simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1185 pattern childGuard
    simpa only [d609, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC207 (pattern : Ten) (guard : d610 pattern = 1) : d152 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d152, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC206 pattern childGuard
    simpa only [d610, d152, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d152, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1187 pattern childGuard
    simpa only [d610, d152, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC208 (pattern : Ten) (guard : d792 pattern = 1) : d154 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d154, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d792, d154, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d154, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC207 pattern childGuard
    simpa only [d792, d154, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC209 (pattern : Ten) (guard : d0 pattern = 1) : d153 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC210 (pattern : Ten) (guard : d611 pattern = 1) : d155 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d155, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC60 pattern childGuard
    simpa only [d611, d155, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d155, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC209 pattern childGuard
    simpa only [d611, d155, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC211 (pattern : Ten) (guard : d793 pattern = 1) : d156 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d156, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC208 pattern childGuard
    simpa only [d793, d156, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d156, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC210 pattern childGuard
    simpa only [d793, d156, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC212 (pattern : Ten) (guard : d606 pattern = 1) : d44 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5144 pattern childGuard
    simpa only [d606, d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c747 pattern childGuard
    simpa only [d606, d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC213 (pattern : Ten) (guard : d0 pattern = 1) : d43 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC214 (pattern : Ten) (guard : d607 pattern = 1) : d50 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d50, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC212 pattern childGuard
    simpa only [d607, d50, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d50, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC213 pattern childGuard
    simpa only [d607, d50, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC215 (pattern : Ten) (guard : d0 pattern = 1) : d51 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC216 (pattern : Ten) (guard : d608 pattern = 1) : d55 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d55, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC214 pattern childGuard
    simpa only [d608, d55, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d55, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC215 pattern childGuard
    simpa only [d608, d55, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC217 (pattern : Ten) (guard : d790 pattern = 1) : d160 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d789 pattern = 1 := by simpa only [d790, d160, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC38 pattern childGuard
    simpa only [d790, d160, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d790, d160, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC216 pattern childGuard
    simpa only [d790, d160, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC218 (pattern : Ten) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC219 (pattern : Ten) (guard : d609 pattern = 1) : d161 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d161, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC46 pattern childGuard
    simpa only [d609, d161, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d161, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC218 pattern childGuard
    simpa only [d609, d161, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC220 (pattern : Ten) (guard : d791 pattern = 1) : d165 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d790 pattern = 1 := by simpa only [d791, d165, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC217 pattern childGuard
    simpa only [d791, d165, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d791, d165, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC219 pattern childGuard
    simpa only [d791, d165, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC221 (pattern : Ten) (guard : d609 pattern = 1) : d162 pattern ≤ (0 : Int) + d811 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d162, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC51 pattern childGuard
    simpa only [d609, d162, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d162, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d609, d162, d811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC222 (pattern : Ten) (guard : d0 pattern = 1) : d163 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC223 (pattern : Ten) (guard : d610 pattern = 1) : d166 pattern ≤ (0 : Int) + d812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d166, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC221 pattern childGuard
    simpa only [d610, d166, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d166, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC222 pattern childGuard
    simpa only [d610, d166, d812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC224 (pattern : Ten) (guard : d792 pattern = 1) : d168 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d791 pattern = 1 := by simpa only [d792, d168, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC220 pattern childGuard
    simpa only [d792, d168, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d792, d168, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC223 pattern childGuard
    simpa only [d792, d168, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC225 (pattern : Ten) (guard : d609 pattern = 1) : d164 pattern ≤ (0 : Int) + d808 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d164, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC58 pattern childGuard
    simpa only [d609, d164, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d164, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1154 pattern childGuard
    simpa only [d609, d164, d808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC226 (pattern : Ten) (guard : d610 pattern = 1) : d167 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d167, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC225 pattern childGuard
    simpa only [d610, d167, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d167, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC92 pattern childGuard
    simpa only [d610, d167, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC227 (pattern : Ten) (guard : d611 pattern = 1) : d169 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d169, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC226 pattern childGuard
    simpa only [d611, d169, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d169, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC61 pattern childGuard
    simpa only [d611, d169, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC228 (pattern : Ten) (guard : d793 pattern = 1) : d170 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d792 pattern = 1 := by simpa only [d793, d170, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC224 pattern childGuard
    simpa only [d793, d170, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d793, d170, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC227 pattern childGuard
    simpa only [d793, d170, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC229 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC230 (pattern : Ten) (guard : d794 pattern = 1) : d171 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d794, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d794, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d794, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC229 pattern childGuard
    simpa only [d794, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC231 (pattern : Ten) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d801 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC232 (pattern : Ten) (guard : d795 pattern = 1) : d176 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d176, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC230 pattern childGuard
    simpa only [d795, d176, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d176, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC231 pattern childGuard
    simpa only [d795, d176, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC233 (pattern : Ten) (guard : d0 pattern = 1) : d177 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC234 (pattern : Ten) (guard : d796 pattern = 1) : d180 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d180, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC232 pattern childGuard
    simpa only [d796, d180, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d180, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC233 pattern childGuard
    simpa only [d796, d180, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC235 (pattern : Ten) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC236 (pattern : Ten) (guard : d797 pattern = 1) : d184 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d184, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC234 pattern childGuard
    simpa only [d797, d184, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d184, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC235 pattern childGuard
    simpa only [d797, d184, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC237 (pattern : Ten) (guard : d0 pattern = 1) : d185 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC238 (pattern : Ten) (guard : d798 pattern = 1) : d188 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d188, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC236 pattern childGuard
    simpa only [d798, d188, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d188, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC237 pattern childGuard
    simpa only [d798, d188, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC239 (pattern : Ten) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC240 (pattern : Ten) (guard : d799 pattern = 1) : d190 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d190, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC238 pattern childGuard
    simpa only [d799, d190, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d190, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC239 pattern childGuard
    simpa only [d799, d190, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC241 (pattern : Ten) (guard : d0 pattern = 1) : d191 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC242 (pattern : Ten) (guard : d800 pattern = 1) : d192 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d192, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC240 pattern childGuard
    simpa only [d800, d192, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d192, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC241 pattern childGuard
    simpa only [d800, d192, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC243 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC244 (pattern : Ten) (guard : d794 pattern = 1) : d174 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d794, d174, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d794, d174, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d794, d174, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC243 pattern childGuard
    simpa only [d794, d174, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC245 (pattern : Ten) (guard : d0 pattern = 1) : d197 pattern ≤ (0 : Int) + d801 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC246 (pattern : Ten) (guard : d795 pattern = 1) : d202 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d202, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC244 pattern childGuard
    simpa only [d795, d202, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d202, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC245 pattern childGuard
    simpa only [d795, d202, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC247 (pattern : Ten) (guard : d0 pattern = 1) : d203 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC248 (pattern : Ten) (guard : d796 pattern = 1) : d207 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d207, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC246 pattern childGuard
    simpa only [d796, d207, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d207, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC247 pattern childGuard
    simpa only [d796, d207, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC249 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC250 (pattern : Ten) (guard : d797 pattern = 1) : d207 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC248 pattern childGuard
    simpa only [d797, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC249 pattern childGuard
    simpa only [d797, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC251 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC252 (pattern : Ten) (guard : d798 pattern = 1) : d207 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC250 pattern childGuard
    simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC251 pattern childGuard
    simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC253 (pattern : Ten) (guard : d0 pattern = 1) : d215 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC254 (pattern : Ten) (guard : d799 pattern = 1) : d218 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC252 pattern childGuard
    simpa only [d799, d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC253 pattern childGuard
    simpa only [d799, d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC255 (pattern : Ten) (guard : d0 pattern = 1) : d219 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC256 (pattern : Ten) (guard : d800 pattern = 1) : d220 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d220, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC254 pattern childGuard
    simpa only [d800, d220, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d220, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC255 pattern childGuard
    simpa only [d800, d220, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC257 (pattern : Ten) (guard : d358 pattern = 1) : d222 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5496 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5611 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC258 (pattern : Ten) (guard : d794 pattern = 1) : d223 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d794, d223, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC257 pattern childGuard
    simpa only [d794, d223, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d794, d223, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c394 pattern childGuard
    simpa only [d794, d223, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC259 (pattern : Ten) (guard : d0 pattern = 1) : d12 pattern ≤ (0 : Int) + d801 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC260 (pattern : Ten) (guard : d795 pattern = 1) : d224 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d224, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC258 pattern childGuard
    simpa only [d795, d224, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d224, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC259 pattern childGuard
    simpa only [d795, d224, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC261 (pattern : Ten) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC262 (pattern : Ten) (guard : d796 pattern = 1) : d225 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d225, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC260 pattern childGuard
    simpa only [d796, d225, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d225, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC261 pattern childGuard
    simpa only [d796, d225, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC263 (pattern : Ten) (guard : d0 pattern = 1) : d26 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC264 (pattern : Ten) (guard : d797 pattern = 1) : d226 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d226, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC262 pattern childGuard
    simpa only [d797, d226, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d226, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC263 pattern childGuard
    simpa only [d797, d226, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC265 (pattern : Ten) (guard : d0 pattern = 1) : d227 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC266 (pattern : Ten) (guard : d798 pattern = 1) : d230 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d230, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC264 pattern childGuard
    simpa only [d798, d230, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d230, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC265 pattern childGuard
    simpa only [d798, d230, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC267 (pattern : Ten) (guard : d0 pattern = 1) : d231 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC268 (pattern : Ten) (guard : d799 pattern = 1) : d232 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d232, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC266 pattern childGuard
    simpa only [d799, d232, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d232, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC267 pattern childGuard
    simpa only [d799, d232, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC269 (pattern : Ten) (guard : d0 pattern = 1) : d233 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC270 (pattern : Ten) (guard : d800 pattern = 1) : d234 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d234, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC268 pattern childGuard
    simpa only [d800, d234, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d234, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC269 pattern childGuard
    simpa only [d800, d234, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC271 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC272 (pattern : Ten) (guard : d798 pattern = 1) : d235 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d235, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC250 pattern childGuard
    simpa only [d798, d235, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d235, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC271 pattern childGuard
    simpa only [d798, d235, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC273 (pattern : Ten) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC274 (pattern : Ten) (guard : d799 pattern = 1) : d236 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d236, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC272 pattern childGuard
    simpa only [d799, d236, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d236, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC273 pattern childGuard
    simpa only [d799, d236, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC275 (pattern : Ten) (guard : d0 pattern = 1) : d237 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC276 (pattern : Ten) (guard : d800 pattern = 1) : d238 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d238, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC274 pattern childGuard
    simpa only [d800, d238, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d238, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC275 pattern childGuard
    simpa only [d800, d238, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC277 (pattern : Ten) (guard : d358 pattern = 1) : d241 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5514 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC278 (pattern : Ten) (guard : d794 pattern = 1) : d242 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d794, d242, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC277 pattern childGuard
    simpa only [d794, d242, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d794, d242, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC229 pattern childGuard
    simpa only [d794, d242, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC279 (pattern : Ten) (guard : d795 pattern = 1) : d243 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d243, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC278 pattern childGuard
    simpa only [d795, d243, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d243, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC231 pattern childGuard
    simpa only [d795, d243, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC280 (pattern : Ten) (guard : d796 pattern = 1) : d244 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d244, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC279 pattern childGuard
    simpa only [d796, d244, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d244, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC233 pattern childGuard
    simpa only [d796, d244, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC281 (pattern : Ten) (guard : d797 pattern = 1) : d245 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d245, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC280 pattern childGuard
    simpa only [d797, d245, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d245, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC235 pattern childGuard
    simpa only [d797, d245, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC282 (pattern : Ten) (guard : d798 pattern = 1) : d246 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d246, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC281 pattern childGuard
    simpa only [d798, d246, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d246, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC237 pattern childGuard
    simpa only [d798, d246, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC283 (pattern : Ten) (guard : d799 pattern = 1) : d247 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d247, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC282 pattern childGuard
    simpa only [d799, d247, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d247, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC239 pattern childGuard
    simpa only [d799, d247, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC284 (pattern : Ten) (guard : d800 pattern = 1) : d248 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d248, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC283 pattern childGuard
    simpa only [d800, d248, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d248, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC241 pattern childGuard
    simpa only [d800, d248, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC285 (pattern : Ten) (guard : d794 pattern = 1) : d173 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d794, d173, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d794, d173, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d794, d173, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1072 pattern childGuard
    simpa only [d794, d173, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC286 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d801 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC287 (pattern : Ten) (guard : d795 pattern = 1) : d249 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d249, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC285 pattern childGuard
    simpa only [d795, d249, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d249, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC286 pattern childGuard
    simpa only [d795, d249, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC288 (pattern : Ten) (guard : d0 pattern = 1) : d250 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC289 (pattern : Ten) (guard : d796 pattern = 1) : d253 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d253, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC287 pattern childGuard
    simpa only [d796, d253, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d253, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC288 pattern childGuard
    simpa only [d796, d253, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC290 (pattern : Ten) (guard : d0 pattern = 1) : d254 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC291 (pattern : Ten) (guard : d797 pattern = 1) : d257 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d257, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC289 pattern childGuard
    simpa only [d797, d257, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d257, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC290 pattern childGuard
    simpa only [d797, d257, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC292 (pattern : Ten) (guard : d0 pattern = 1) : d258 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC293 (pattern : Ten) (guard : d798 pattern = 1) : d261 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d261, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC291 pattern childGuard
    simpa only [d798, d261, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d261, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC292 pattern childGuard
    simpa only [d798, d261, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC294 (pattern : Ten) (guard : d0 pattern = 1) : d262 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC295 (pattern : Ten) (guard : d799 pattern = 1) : d263 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d263, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC293 pattern childGuard
    simpa only [d799, d263, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d263, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC294 pattern childGuard
    simpa only [d799, d263, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC296 (pattern : Ten) (guard : d0 pattern = 1) : d264 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC297 (pattern : Ten) (guard : d800 pattern = 1) : d265 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d265, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC295 pattern childGuard
    simpa only [d800, d265, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d265, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC296 pattern childGuard
    simpa only [d800, d265, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC298 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d801 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC299 (pattern : Ten) (guard : d795 pattern = 1) : d266 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d266, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC244 pattern childGuard
    simpa only [d795, d266, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d266, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC298 pattern childGuard
    simpa only [d795, d266, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC300 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC301 (pattern : Ten) (guard : d796 pattern = 1) : d267 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d267, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC299 pattern childGuard
    simpa only [d796, d267, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d267, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC300 pattern childGuard
    simpa only [d796, d267, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC302 (pattern : Ten) (guard : d0 pattern = 1) : d268 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC303 (pattern : Ten) (guard : d797 pattern = 1) : d271 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d271, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC301 pattern childGuard
    simpa only [d797, d271, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d271, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC302 pattern childGuard
    simpa only [d797, d271, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC304 (pattern : Ten) (guard : d0 pattern = 1) : d272 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC305 (pattern : Ten) (guard : d798 pattern = 1) : d275 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d275, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC303 pattern childGuard
    simpa only [d798, d275, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d275, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC304 pattern childGuard
    simpa only [d798, d275, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC306 (pattern : Ten) (guard : d0 pattern = 1) : d276 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC307 (pattern : Ten) (guard : d799 pattern = 1) : d277 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d277, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC305 pattern childGuard
    simpa only [d799, d277, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d277, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC306 pattern childGuard
    simpa only [d799, d277, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC308 (pattern : Ten) (guard : d0 pattern = 1) : d278 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC309 (pattern : Ten) (guard : d800 pattern = 1) : d279 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d279, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC307 pattern childGuard
    simpa only [d800, d279, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d279, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC308 pattern childGuard
    simpa only [d800, d279, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC310 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC311 (pattern : Ten) (guard : d796 pattern = 1) : d280 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d280, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC246 pattern childGuard
    simpa only [d796, d280, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d280, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC310 pattern childGuard
    simpa only [d796, d280, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC312 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC313 (pattern : Ten) (guard : d797 pattern = 1) : d281 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d281, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC311 pattern childGuard
    simpa only [d797, d281, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d281, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC312 pattern childGuard
    simpa only [d797, d281, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC314 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC315 (pattern : Ten) (guard : d798 pattern = 1) : d284 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d284, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC313 pattern childGuard
    simpa only [d798, d284, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d284, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC314 pattern childGuard
    simpa only [d798, d284, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC316 (pattern : Ten) (guard : d0 pattern = 1) : d285 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC317 (pattern : Ten) (guard : d799 pattern = 1) : d286 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d286, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC315 pattern childGuard
    simpa only [d799, d286, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d286, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC316 pattern childGuard
    simpa only [d799, d286, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC318 (pattern : Ten) (guard : d0 pattern = 1) : d287 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC319 (pattern : Ten) (guard : d800 pattern = 1) : d288 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d288, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC317 pattern childGuard
    simpa only [d800, d288, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d288, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC318 pattern childGuard
    simpa only [d800, d288, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
