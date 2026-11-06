import NetHack.Soko22Hazard87.Compare166
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41750 (p : Pattern) (guard : d348652 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348647 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41745 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41751 (p : Pattern) (guard : d348653 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348652 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41750 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41752 (p : Pattern) (guard : d348654 p = 1) : d50932 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348653 p = 1 := by simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41751 p hg
    simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41753 (p : Pattern) (guard : d348655 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348654 p = 1 := by simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41752 p hg
    simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41754 (p : Pattern) (guard : d348656 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41749 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348655 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41753 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41755 (p : Pattern) (guard : d348657 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348656 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41754 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41756 (p : Pattern) (guard : d348658 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348657 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41755 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41757 (p : Pattern) (guard : d348659 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348658 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41756 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41758 (p : Pattern) (guard : d348660 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348655 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41753 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41759 (p : Pattern) (guard : d348661 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348660 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41758 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41760 (p : Pattern) (guard : d348662 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348661 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41759 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41761 (p : Pattern) (guard : d348663 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348662 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41760 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41762 (p : Pattern) (guard : d348664 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348659 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41757 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348663 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41761 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41763 (p : Pattern) (guard : d348665 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348664 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41762 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41764 (p : Pattern) (guard : d348666 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348665 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41763 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41765 (p : Pattern) (guard : d348667 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348666 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41764 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41766 (p : Pattern) (guard : d348668 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348667 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41765 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41767 (p : Pattern) (guard : d348672 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348658 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41728 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41768 (p : Pattern) (guard : d348673 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348662 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41732 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41769 (p : Pattern) (guard : d348674 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348672 p = 1 := by simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41767 p hg
    simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348673 p = 1 := by simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41768 p hg
    simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41770 (p : Pattern) (guard : d348675 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348674 p = 1 := by simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41769 p hg
    simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41771 (p : Pattern) (guard : d348676 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348675 p = 1 := by simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41770 p hg
    simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41772 (p : Pattern) (guard : d348677 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348676 p = 1 := by simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41771 p hg
    simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41773 (p : Pattern) (guard : d348678 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348677 p = 1 := by simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41772 p hg
    simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41774 (p : Pattern) (guard : d348679 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348668 p = 1 := by simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41766 p hg
    simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348678 p = 1 := by simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41773 p hg
    simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41775 (p : Pattern) (guard : d348680 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348669 p = 1 := by simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41739 p hg
    simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348679 p = 1 := by simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41774 p hg
    simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41776 (p : Pattern) (guard : d348681 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348680 p = 1 := by simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41775 p hg
    simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41777 (p : Pattern) (guard : d348682 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348671 p = 1 := by simpa only [d348682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41741 p hg
    simpa only [d348682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348681 p = 1 := by simpa only [d348682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41776 p hg
    simpa only [d348682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41778 (p : Pattern) (guard : d348683 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348657 p = 1 := by simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41727 p hg
    simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41779 (p : Pattern) (guard : d348684 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348683 p = 1 := by simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41778 p hg
    simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41780 (p : Pattern) (guard : d348685 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348661 p = 1 := by simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41731 p hg
    simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41781 (p : Pattern) (guard : d348686 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348685 p = 1 := by simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41780 p hg
    simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41782 (p : Pattern) (guard : d348687 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348684 p = 1 := by simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41779 p hg
    simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348686 p = 1 := by simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41781 p hg
    simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41783 (p : Pattern) (guard : d348688 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348687 p = 1 := by simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41782 p hg
    simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41784 (p : Pattern) (guard : d348689 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348688 p = 1 := by simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41783 p hg
    simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41785 (p : Pattern) (guard : d348690 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348689 p = 1 := by simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41784 p hg
    simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41786 (p : Pattern) (guard : d348691 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348656 p = 1 := by simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41726 p hg
    simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41787 (p : Pattern) (guard : d348692 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348691 p = 1 := by simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41786 p hg
    simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41788 (p : Pattern) (guard : d348693 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348692 p = 1 := by simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41789 (p : Pattern) (guard : d348694 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348660 p = 1 := by simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41730 p hg
    simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41790 (p : Pattern) (guard : d348695 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348694 p = 1 := by simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41789 p hg
    simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41791 (p : Pattern) (guard : d348696 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348695 p = 1 := by simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41790 p hg
    simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41792 (p : Pattern) (guard : d348697 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348693 p = 1 := by simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41788 p hg
    simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348696 p = 1 := by simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41791 p hg
    simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41793 (p : Pattern) (guard : d348698 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348697 p = 1 := by simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41792 p hg
    simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41794 (p : Pattern) (guard : d348699 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348698 p = 1 := by simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41793 p hg
    simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41795 (p : Pattern) (guard : d348700 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348637 p = 1 := by simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41707 p hg
    simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41796 (p : Pattern) (guard : d348701 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348701, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348701, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348700 p = 1 := by simpa only [d348701, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41795 p hg
    simpa only [d348701, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41797 (p : Pattern) (guard : d348702 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348702, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348702, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348701 p = 1 := by simpa only [d348702, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41796 p hg
    simpa only [d348702, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41798 (p : Pattern) (guard : d348703 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348636 p = 1 := by simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41706 p hg
    simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348638 p = 1 := by simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41708 p hg
    simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41799 (p : Pattern) (guard : d348704 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348637 p = 1 := by simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41707 p hg
    simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348703 p = 1 := by simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41798 p hg
    simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41800 (p : Pattern) (guard : d348705 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348705, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348705, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348704 p = 1 := by simpa only [d348705, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41799 p hg
    simpa only [d348705, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41801 (p : Pattern) (guard : d348706 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348706, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348706, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348705 p = 1 := by simpa only [d348706, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41800 p hg
    simpa only [d348706, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41802 (p : Pattern) (guard : d348707 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348702 p = 1 := by simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41797 p hg
    simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348706 p = 1 := by simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41801 p hg
    simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41803 (p : Pattern) (guard : d348708 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348707 p = 1 := by simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41802 p hg
    simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348646 p = 1 := by simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41716 p hg
    simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41804 (p : Pattern) (guard : d348709 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348708 p = 1 := by simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41803 p hg
    simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41805 (p : Pattern) (guard : d348710 p = 1) : d50953 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348709 p = 1 := by simpa only [d348710, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41804 p hg
    simpa only [d348710, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348710, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348710, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41806 (p : Pattern) (guard : d348711 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348711, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348711, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348710 p = 1 := by simpa only [d348711, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41805 p hg
    simpa only [d348711, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41807 (p : Pattern) (guard : d348712 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348711 p = 1 := by simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41806 p hg
    simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348651 p = 1 := by simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41721 p hg
    simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41808 (p : Pattern) (guard : d348713 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348712 p = 1 := by simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41807 p hg
    simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41809 (p : Pattern) (guard : d348714 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348713 p = 1 := by simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41808 p hg
    simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41810 (p : Pattern) (guard : d348715 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348714 p = 1 := by simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41809 p hg
    simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41811 (p : Pattern) (guard : d348716 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348715 p = 1 := by simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41810 p hg
    simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348659 p = 1 := by simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41729 p hg
    simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41812 (p : Pattern) (guard : d348717 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348716 p = 1 := by simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41811 p hg
    simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41813 (p : Pattern) (guard : d348718 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41721 p hg
    simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41814 (p : Pattern) (guard : d348719 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348718 p = 1 := by simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41813 p hg
    simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41815 (p : Pattern) (guard : d348720 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348719 p = 1 := by simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41814 p hg
    simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41816 (p : Pattern) (guard : d348721 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348720 p = 1 := by simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41815 p hg
    simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41817 (p : Pattern) (guard : d348722 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348721 p = 1 := by simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41816 p hg
    simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41818 (p : Pattern) (guard : d348723 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348722 p = 1 := by simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41817 p hg
    simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41819 (p : Pattern) (guard : d348724 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348717 p = 1 := by simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41812 p hg
    simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348723 p = 1 := by simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41818 p hg
    simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41820 (p : Pattern) (guard : d348725 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d348699 p = 1 := by simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41794 p hg
    simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348724 p = 1 := by simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41819 p hg
    simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41821 (p : Pattern) (guard : d348726 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d348690 p = 1 := by simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41785 p hg
    simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348725 p = 1 := by simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41820 p hg
    simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41822 (p : Pattern) (guard : d348727 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348727, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348727, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348726 p = 1 := by simpa only [d348727, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41821 p hg
    simpa only [d348727, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41823 (p : Pattern) (guard : d348683 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348657 p = 1 := by simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41755 p hg
    simpa only [d348683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41824 (p : Pattern) (guard : d348684 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348683 p = 1 := by simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41823 p hg
    simpa only [d348684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41825 (p : Pattern) (guard : d348685 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348661 p = 1 := by simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41759 p hg
    simpa only [d348685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41826 (p : Pattern) (guard : d348686 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348685 p = 1 := by simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41825 p hg
    simpa only [d348686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41827 (p : Pattern) (guard : d348687 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348684 p = 1 := by simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41824 p hg
    simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348686 p = 1 := by simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41826 p hg
    simpa only [d348687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41828 (p : Pattern) (guard : d348688 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348687 p = 1 := by simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41827 p hg
    simpa only [d348688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41829 (p : Pattern) (guard : d348689 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348688 p = 1 := by simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41828 p hg
    simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41830 (p : Pattern) (guard : d348690 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348689 p = 1 := by simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41829 p hg
    simpa only [d348690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41831 (p : Pattern) (guard : d348691 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348656 p = 1 := by simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41754 p hg
    simpa only [d348691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41832 (p : Pattern) (guard : d348692 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348691 p = 1 := by simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41831 p hg
    simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41833 (p : Pattern) (guard : d348693 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348692 p = 1 := by simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41832 p hg
    simpa only [d348693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41834 (p : Pattern) (guard : d348694 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348660 p = 1 := by simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41758 p hg
    simpa only [d348694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41835 (p : Pattern) (guard : d348695 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348694 p = 1 := by simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41834 p hg
    simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41836 (p : Pattern) (guard : d348696 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348695 p = 1 := by simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41835 p hg
    simpa only [d348696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41837 (p : Pattern) (guard : d348697 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348693 p = 1 := by simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41833 p hg
    simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348696 p = 1 := by simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41836 p hg
    simpa only [d348697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41838 (p : Pattern) (guard : d348698 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348697 p = 1 := by simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41837 p hg
    simpa only [d348698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41839 (p : Pattern) (guard : d348699 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348698 p = 1 := by simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41838 p hg
    simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41840 (p : Pattern) (guard : d348702 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348702, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348702, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348701 p = 1 := by simpa only [d348702, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41796 p hg
    simpa only [d348702, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41841 (p : Pattern) (guard : d348706 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348706, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348706, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348705 p = 1 := by simpa only [d348706, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41800 p hg
    simpa only [d348706, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41842 (p : Pattern) (guard : d348707 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348702 p = 1 := by simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41840 p hg
    simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348706 p = 1 := by simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41841 p hg
    simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41843 (p : Pattern) (guard : d348708 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348707 p = 1 := by simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41842 p hg
    simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348646 p = 1 := by simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41744 p hg
    simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41844 (p : Pattern) (guard : d348709 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348708 p = 1 := by simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41843 p hg
    simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41845 (p : Pattern) (guard : d348710 p = 1) : d50932 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348709 p = 1 := by simpa only [d348710, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41844 p hg
    simpa only [d348710, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348710, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348710, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41846 (p : Pattern) (guard : d348711 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348711, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d348711, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348710 p = 1 := by simpa only [d348711, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41845 p hg
    simpa only [d348711, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41847 (p : Pattern) (guard : d348712 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348711 p = 1 := by simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41846 p hg
    simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348651 p = 1 := by simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41749 p hg
    simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41848 (p : Pattern) (guard : d348713 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348712 p = 1 := by simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41847 p hg
    simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41849 (p : Pattern) (guard : d348714 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348713 p = 1 := by simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41848 p hg
    simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41850 (p : Pattern) (guard : d348715 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348714 p = 1 := by simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41849 p hg
    simpa only [d348715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41851 (p : Pattern) (guard : d348716 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348715 p = 1 := by simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41850 p hg
    simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348659 p = 1 := by simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41757 p hg
    simpa only [d348716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41852 (p : Pattern) (guard : d348717 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348716 p = 1 := by simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41853 (p : Pattern) (guard : d348718 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41749 p hg
    simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41854 (p : Pattern) (guard : d348719 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348718 p = 1 := by simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41853 p hg
    simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41855 (p : Pattern) (guard : d348720 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348719 p = 1 := by simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41856 (p : Pattern) (guard : d348721 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348720 p = 1 := by simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41855 p hg
    simpa only [d348721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41857 (p : Pattern) (guard : d348722 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348721 p = 1 := by simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41856 p hg
    simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41858 (p : Pattern) (guard : d348723 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348722 p = 1 := by simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41857 p hg
    simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41859 (p : Pattern) (guard : d348724 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348717 p = 1 := by simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41852 p hg
    simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348723 p = 1 := by simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41858 p hg
    simpa only [d348724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41860 (p : Pattern) (guard : d348725 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d348699 p = 1 := by simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41839 p hg
    simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348724 p = 1 := by simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41859 p hg
    simpa only [d348725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41861 (p : Pattern) (guard : d348726 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d348690 p = 1 := by simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41830 p hg
    simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348725 p = 1 := by simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41860 p hg
    simpa only [d348726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41862 (p : Pattern) (guard : d348728 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348683 p = 1 := by simpa only [d348728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41778 p hg
    simpa only [d348728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41863 (p : Pattern) (guard : d348729 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348685 p = 1 := by simpa only [d348729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41780 p hg
    simpa only [d348729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41864 (p : Pattern) (guard : d348730 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348728 p = 1 := by simpa only [d348730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41862 p hg
    simpa only [d348730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348729 p = 1 := by simpa only [d348730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41863 p hg
    simpa only [d348730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41865 (p : Pattern) (guard : d348731 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348730 p = 1 := by simpa only [d348731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41864 p hg
    simpa only [d348731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41866 (p : Pattern) (guard : d348732 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348731 p = 1 := by simpa only [d348732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41865 p hg
    simpa only [d348732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41867 (p : Pattern) (guard : d348733 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348732 p = 1 := by simpa only [d348733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41866 p hg
    simpa only [d348733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41868 (p : Pattern) (guard : d348734 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348692 p = 1 := by simpa only [d348734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d348734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41869 (p : Pattern) (guard : d348735 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348695 p = 1 := by simpa only [d348735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41790 p hg
    simpa only [d348735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41870 (p : Pattern) (guard : d348736 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348734 p = 1 := by simpa only [d348736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41868 p hg
    simpa only [d348736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348735 p = 1 := by simpa only [d348736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d348736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41871 (p : Pattern) (guard : d348737 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348736 p = 1 := by simpa only [d348737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41870 p hg
    simpa only [d348737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41872 (p : Pattern) (guard : d348738 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348737 p = 1 := by simpa only [d348738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41871 p hg
    simpa only [d348738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41873 (p : Pattern) (guard : d348739 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348714 p = 1 := by simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41809 p hg
    simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41874 (p : Pattern) (guard : d348740 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348739 p = 1 := by simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41873 p hg
    simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348672 p = 1 := by simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41767 p hg
    simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41875 (p : Pattern) (guard : d348741 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348740 p = 1 := by simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41874 p hg
    simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41876 (p : Pattern) (guard : d348742 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348720 p = 1 := by simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41815 p hg
    simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41877 (p : Pattern) (guard : d348743 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348742 p = 1 := by simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41876 p hg
    simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41878 (p : Pattern) (guard : d348744 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348743 p = 1 := by simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41877 p hg
    simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41879 (p : Pattern) (guard : d348745 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348741 p = 1 := by simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41875 p hg
    simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348744 p = 1 := by simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41878 p hg
    simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41880 (p : Pattern) (guard : d348746 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d348738 p = 1 := by simpa only [d348746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d348746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348745 p = 1 := by simpa only [d348746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41879 p hg
    simpa only [d348746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41881 (p : Pattern) (guard : d348747 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d348733 p = 1 := by simpa only [d348747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41867 p hg
    simpa only [d348747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348746 p = 1 := by simpa only [d348747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41880 p hg
    simpa only [d348747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41882 (p : Pattern) (guard : d348748 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348726 p = 1 := by simpa only [d348748, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41861 p hg
    simpa only [d348748, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348747 p = 1 := by simpa only [d348748, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41881 p hg
    simpa only [d348748, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41883 (p : Pattern) (guard : d348749 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348727 p = 1 := by simpa only [d348749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41822 p hg
    simpa only [d348749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348748 p = 1 := by simpa only [d348749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41882 p hg
    simpa only [d348749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41884 (p : Pattern) (guard : d348750 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348663 p = 1 := by simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41733 p hg
    simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41885 (p : Pattern) (guard : d348751 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348750 p = 1 := by simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41884 p hg
    simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41886 (p : Pattern) (guard : d348752 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348751 p = 1 := by simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41885 p hg
    simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41887 (p : Pattern) (guard : d348753 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348752 p = 1 := by simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41886 p hg
    simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41888 (p : Pattern) (guard : d348754 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348753 p = 1 := by simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41887 p hg
    simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41889 (p : Pattern) (guard : d348755 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348668 p = 1 := by simpa only [d348755, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41766 p hg
    simpa only [d348755, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348754 p = 1 := by simpa only [d348755, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41888 p hg
    simpa only [d348755, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41890 (p : Pattern) (guard : d348750 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348663 p = 1 := by simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41761 p hg
    simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41891 (p : Pattern) (guard : d348751 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348750 p = 1 := by simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41890 p hg
    simpa only [d348751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41892 (p : Pattern) (guard : d348752 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348751 p = 1 := by simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41891 p hg
    simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41893 (p : Pattern) (guard : d348753 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348752 p = 1 := by simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41892 p hg
    simpa only [d348753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41894 (p : Pattern) (guard : d348754 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348753 p = 1 := by simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41893 p hg
    simpa only [d348754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41895 (p : Pattern) (guard : d348756 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348673 p = 1 := by simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41768 p hg
    simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41896 (p : Pattern) (guard : d348757 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348756 p = 1 := by simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41895 p hg
    simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41897 (p : Pattern) (guard : d348758 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348757 p = 1 := by simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41896 p hg
    simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41898 (p : Pattern) (guard : d348759 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348758 p = 1 := by simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41897 p hg
    simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41899 (p : Pattern) (guard : d348760 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348759 p = 1 := by simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41898 p hg
    simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41900 (p : Pattern) (guard : d348761 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348754 p = 1 := by simpa only [d348761, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41894 p hg
    simpa only [d348761, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348760 p = 1 := by simpa only [d348761, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41899 p hg
    simpa only [d348761, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41901 (p : Pattern) (guard : d348762 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348755 p = 1 := by simpa only [d348762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41889 p hg
    simpa only [d348762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348761 p = 1 := by simpa only [d348762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41900 p hg
    simpa only [d348762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41902 (p : Pattern) (guard : d348763 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348749 p = 1 := by simpa only [d348763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41883 p hg
    simpa only [d348763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348762 p = 1 := by simpa only [d348763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41901 p hg
    simpa only [d348763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41903 (p : Pattern) (guard : d348764 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348763 p = 1 := by simpa only [d348764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41902 p hg
    simpa only [d348764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41904 (p : Pattern) (guard : d348765 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348682 p = 1 := by simpa only [d348765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41777 p hg
    simpa only [d348765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348764 p = 1 := by simpa only [d348765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41903 p hg
    simpa only [d348765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41905 (p : Pattern) (guard : d308 p = 1) : d5 p ≤ (1 : Int) + d5 p := by
  omega
theorem compare41906 (p : Pattern) (guard : d1519 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41905 p hg
    simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41466 p hg
    simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41907 (p : Pattern) (guard : d1531 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41906 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41908 (p : Pattern) (guard : d1547 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41907 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41909 (p : Pattern) (guard : d39244 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41908 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41910 (p : Pattern) (guard : d337457 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41909 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41911 (p : Pattern) (guard : d337458 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41910 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41912 (p : Pattern) (guard : d337473 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41911 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41913 (p : Pattern) (guard : d258107 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41909 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41914 (p : Pattern) (guard : d258108 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41913 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41915 (p : Pattern) (guard : d258109 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41914 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41916 (p : Pattern) (guard : d348629 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41912 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41915 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41917 (p : Pattern) (guard : d348630 p = 1) : d50967 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41916 p hg
    simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41478 p hg
    simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41918 (p : Pattern) (guard : d348631 p = 1) : d50967 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41917 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41480 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41919 (p : Pattern) (guard : d348632 p = 1) : d50997 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41918 p hg
    simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41482 p hg
    simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41920 (p : Pattern) (guard : d348633 p = 1) : d50998 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348632 p = 1 := by simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41919 p hg
    simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41921 (p : Pattern) (guard : d348634 p = 1) : d51018 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41463 p hg
    simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348633 p = 1 := by simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41920 p hg
    simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41922 (p : Pattern) (guard : d348635 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348634 p = 1 := by simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41921 p hg
    simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41486 p hg
    simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41923 (p : Pattern) (guard : d348636 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348635 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41922 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41924 (p : Pattern) (guard : d348637 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348636 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41923 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41925 (p : Pattern) (guard : d348700 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348637 p = 1 := by simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41924 p hg
    simpa only [d348700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41926 (p : Pattern) (guard : d348701 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348701, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348701, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348700 p = 1 := by simpa only [d348701, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41925 p hg
    simpa only [d348701, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41927 (p : Pattern) (guard : d348702 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348702, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348702, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348701 p = 1 := by simpa only [d348702, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41926 p hg
    simpa only [d348702, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41928 (p : Pattern) (guard : d348638 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348635 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41922 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41929 (p : Pattern) (guard : d348703 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348636 p = 1 := by simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41923 p hg
    simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348638 p = 1 := by simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41928 p hg
    simpa only [d348703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41930 (p : Pattern) (guard : d348704 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348637 p = 1 := by simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41924 p hg
    simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348703 p = 1 := by simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41929 p hg
    simpa only [d348704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41931 (p : Pattern) (guard : d348705 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348705, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348705, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348704 p = 1 := by simpa only [d348705, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41930 p hg
    simpa only [d348705, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41932 (p : Pattern) (guard : d348706 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348706, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348706, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348705 p = 1 := by simpa only [d348706, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41931 p hg
    simpa only [d348706, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41933 (p : Pattern) (guard : d348707 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348702 p = 1 := by simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41927 p hg
    simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348706 p = 1 := by simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41932 p hg
    simpa only [d348707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41934 (p : Pattern) (guard : d348639 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348638 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41928 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41935 (p : Pattern) (guard : d348640 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348637 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41924 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348639 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41934 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41936 (p : Pattern) (guard : d348641 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348640 p = 1 := by simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41935 p hg
    simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41937 (p : Pattern) (guard : d348642 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348641 p = 1 := by simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41936 p hg
    simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41938 (p : Pattern) (guard : d348643 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348639 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41934 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41939 (p : Pattern) (guard : d348644 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348643 p = 1 := by simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41938 p hg
    simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41940 (p : Pattern) (guard : d348645 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348644 p = 1 := by simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41939 p hg
    simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41941 (p : Pattern) (guard : d348646 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348642 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41937 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348645 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41940 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41942 (p : Pattern) (guard : d348708 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348707 p = 1 := by simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41933 p hg
    simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348646 p = 1 := by simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41941 p hg
    simpa only [d348708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41943 (p : Pattern) (guard : d348709 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348708 p = 1 := by simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41942 p hg
    simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41944 (p : Pattern) (guard : d348710 p = 1) : d51036 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348709 p = 1 := by simpa only [d348710, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41943 p hg
    simpa only [d348710, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348710, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d348710, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41945 (p : Pattern) (guard : d348711 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348711, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d348711, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348710 p = 1 := by simpa only [d348711, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41944 p hg
    simpa only [d348711, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41946 (p : Pattern) (guard : d348647 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348645 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41940 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41947 (p : Pattern) (guard : d348648 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348646 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41941 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348647 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41948 (p : Pattern) (guard : d348649 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348648 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41947 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41949 (p : Pattern) (guard : d348650 p = 1) : d51036 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348649 p = 1 := by simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41948 p hg
    simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41950 (p : Pattern) (guard : d348651 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348650 p = 1 := by simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41951 (p : Pattern) (guard : d348712 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348711 p = 1 := by simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41945 p hg
    simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348651 p = 1 := by simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41950 p hg
    simpa only [d348712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41952 (p : Pattern) (guard : d348713 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348712 p = 1 := by simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41951 p hg
    simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41953 (p : Pattern) (guard : d348714 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348713 p = 1 := by simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41952 p hg
    simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41954 (p : Pattern) (guard : d348739 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348714 p = 1 := by simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41953 p hg
    simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41955 (p : Pattern) (guard : d348652 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348647 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41956 (p : Pattern) (guard : d348653 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348652 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41955 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41957 (p : Pattern) (guard : d348654 p = 1) : d51036 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348653 p = 1 := by simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41956 p hg
    simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41958 (p : Pattern) (guard : d348655 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348654 p = 1 := by simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41957 p hg
    simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41959 (p : Pattern) (guard : d348656 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41950 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348655 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41958 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41960 (p : Pattern) (guard : d348657 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348656 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41959 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41961 (p : Pattern) (guard : d348658 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348657 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41960 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41962 (p : Pattern) (guard : d348672 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348658 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41961 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41963 (p : Pattern) (guard : d348740 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348739 p = 1 := by simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41954 p hg
    simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348672 p = 1 := by simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41962 p hg
    simpa only [d348740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41964 (p : Pattern) (guard : d348741 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348740 p = 1 := by simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41963 p hg
    simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41965 (p : Pattern) (guard : d348718 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41950 p hg
    simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41966 (p : Pattern) (guard : d348719 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348718 p = 1 := by simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41965 p hg
    simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41967 (p : Pattern) (guard : d348720 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348719 p = 1 := by simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41966 p hg
    simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41968 (p : Pattern) (guard : d348742 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348720 p = 1 := by simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41967 p hg
    simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41969 (p : Pattern) (guard : d348743 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348742 p = 1 := by simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41968 p hg
    simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41970 (p : Pattern) (guard : d348744 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348743 p = 1 := by simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41969 p hg
    simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41971 (p : Pattern) (guard : d348745 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348741 p = 1 := by simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41964 p hg
    simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348744 p = 1 := by simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41970 p hg
    simpa only [d348745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41972 (p : Pattern) (guard : d348766 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348745 p = 1 := by simpa only [d348766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41971 p hg
    simpa only [d348766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41973 (p : Pattern) (guard : d348767 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348766 p = 1 := by simpa only [d348767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41972 p hg
    simpa only [d348767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41974 (p : Pattern) (guard : d348768 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348768, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348768, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348767 p = 1 := by simpa only [d348768, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41973 p hg
    simpa only [d348768, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41975 (p : Pattern) (guard : d348769 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348768 p = 1 := by simpa only [d348769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41974 p hg
    simpa only [d348769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41976 (p : Pattern) (guard : d348660 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348655 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41958 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41977 (p : Pattern) (guard : d348661 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348660 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41976 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41978 (p : Pattern) (guard : d348662 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348661 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41977 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41979 (p : Pattern) (guard : d348673 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348662 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41978 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41980 (p : Pattern) (guard : d348756 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348673 p = 1 := by simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41979 p hg
    simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41981 (p : Pattern) (guard : d348757 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348756 p = 1 := by simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41980 p hg
    simpa only [d348757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41982 (p : Pattern) (guard : d348758 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348757 p = 1 := by simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41981 p hg
    simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41983 (p : Pattern) (guard : d348759 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348758 p = 1 := by simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41982 p hg
    simpa only [d348759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41984 (p : Pattern) (guard : d348760 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348759 p = 1 := by simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41983 p hg
    simpa only [d348760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41985 (p : Pattern) (guard : d348770 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348770, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348770, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348760 p = 1 := by simpa only [d348770, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41984 p hg
    simpa only [d348770, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41986 (p : Pattern) (guard : d348771 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348770 p = 1 := by simpa only [d348771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41985 p hg
    simpa only [d348771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41987 (p : Pattern) (guard : d348772 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348769 p = 1 := by simpa only [d348772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41975 p hg
    simpa only [d348772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348771 p = 1 := by simpa only [d348772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41986 p hg
    simpa only [d348772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41988 (p : Pattern) (guard : d348773 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348772 p = 1 := by simpa only [d348773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41987 p hg
    simpa only [d348773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41989 (p : Pattern) (guard : d348774 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348773 p = 1 := by simpa only [d348774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41988 p hg
    simpa only [d348774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41990 (p : Pattern) (guard : d348775 p = 1) : d51039 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d348765 p = 1 := by simpa only [d348775, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41904 p hg
    simpa only [d348775, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348774 p = 1 := by simpa only [d348775, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41989 p hg
    simpa only [d348775, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41991 (p : Pattern) (guard : d308 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare41992 (p : Pattern) (guard : d1519 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41991 p hg
    simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41566 p hg
    simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41993 (p : Pattern) (guard : d1531 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41992 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41994 (p : Pattern) (guard : d1547 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41993 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41995 (p : Pattern) (guard : d39244 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41994 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41996 (p : Pattern) (guard : d337457 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41995 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41997 (p : Pattern) (guard : d337458 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41996 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41998 (p : Pattern) (guard : d337473 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41997 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41999 (p : Pattern) (guard : d258107 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41995 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
