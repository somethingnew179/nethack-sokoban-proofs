import NetHack.Soko22Hazard87.Compare063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16000 (p : Pattern) (guard : d17195 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17194 p = 1 := by simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15999 p hg
    simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16001 (p : Pattern) (guard : d17196 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17195 p = 1 := by simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16000 p hg
    simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16002 (p : Pattern) (guard : d17164 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15957 p hg
    simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16003 (p : Pattern) (guard : d17167 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15967 p hg
    simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16004 (p : Pattern) (guard : d17168 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16002 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16003 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16005 (p : Pattern) (guard : d17171 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15975 p hg
    simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16006 (p : Pattern) (guard : d17172 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16005 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16007 (p : Pattern) (guard : d17173 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16006 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16008 (p : Pattern) (guard : d17174 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16007 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16009 (p : Pattern) (guard : d17175 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16008 p hg
    simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16010 (p : Pattern) (guard : d17176 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16009 p hg
    simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16011 (p : Pattern) (guard : d17177 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16006 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16012 (p : Pattern) (guard : d17178 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16011 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16013 (p : Pattern) (guard : d17179 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16012 p hg
    simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16014 (p : Pattern) (guard : d17180 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16013 p hg
    simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16015 (p : Pattern) (guard : d17181 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16010 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16014 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16016 (p : Pattern) (guard : d17182 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16015 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16017 (p : Pattern) (guard : d17183 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16016 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16018 (p : Pattern) (guard : d17184 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16017 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16019 (p : Pattern) (guard : d17185 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16014 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16020 (p : Pattern) (guard : d17186 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16019 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16021 (p : Pattern) (guard : d17187 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16022 (p : Pattern) (guard : d17188 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16021 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16023 (p : Pattern) (guard : d17189 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16018 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16022 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16024 (p : Pattern) (guard : d17190 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16023 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16025 (p : Pattern) (guard : d17191 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16024 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16026 (p : Pattern) (guard : d17192 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16025 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16027 (p : Pattern) (guard : d17193 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16026 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16028 (p : Pattern) (guard : d17197 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17183 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15988 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16029 (p : Pattern) (guard : d17198 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15992 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16030 (p : Pattern) (guard : d17199 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17197 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16028 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17198 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16029 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16031 (p : Pattern) (guard : d17200 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17199 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16030 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16032 (p : Pattern) (guard : d17201 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17200 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16031 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16033 (p : Pattern) (guard : d17202 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17201 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16032 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16034 (p : Pattern) (guard : d17203 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17202 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16033 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16035 (p : Pattern) (guard : d17204 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17193 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16027 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17203 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16034 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16036 (p : Pattern) (guard : d17205 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d17194 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15999 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17204 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16035 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16037 (p : Pattern) (guard : d17206 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17205 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16036 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16038 (p : Pattern) (guard : d17207 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d17196 p = 1 := by simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16001 p hg
    simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17206 p = 1 := by simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16037 p hg
    simpa only [d17207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16039 (p : Pattern) (guard : d17208 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17182 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15987 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16040 (p : Pattern) (guard : d17209 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17208 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16039 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16041 (p : Pattern) (guard : d17210 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17186 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15991 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16042 (p : Pattern) (guard : d17211 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17210 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16041 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16043 (p : Pattern) (guard : d17212 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17209 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16040 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17211 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16042 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16044 (p : Pattern) (guard : d17213 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17212 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16043 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16045 (p : Pattern) (guard : d17214 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17213 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16044 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16046 (p : Pattern) (guard : d17215 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17214 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16045 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16047 (p : Pattern) (guard : d17216 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17181 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15986 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16048 (p : Pattern) (guard : d17217 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17216 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16047 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16049 (p : Pattern) (guard : d17218 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17217 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16048 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16050 (p : Pattern) (guard : d17219 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17185 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15990 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16051 (p : Pattern) (guard : d17220 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17219 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16050 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16052 (p : Pattern) (guard : d17221 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17220 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16051 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16053 (p : Pattern) (guard : d17222 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17218 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16049 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17221 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16052 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16054 (p : Pattern) (guard : d17223 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17222 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16053 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16055 (p : Pattern) (guard : d17224 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17223 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16054 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16056 (p : Pattern) (guard : d2146 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare16057 (p : Pattern) (guard : d2147 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16056 p hg
    simpa only [d2147, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d2147, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16058 (p : Pattern) (guard : d17225 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare16059 (p : Pattern) (guard : d17226 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16058 p hg
    simpa only [d17226, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d17226, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16060 (p : Pattern) (guard : d17227 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16057 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16059 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16061 (p : Pattern) (guard : d17228 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13676 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15944 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16062 (p : Pattern) (guard : d17229 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17227 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16060 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17228 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16061 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16063 (p : Pattern) (guard : d17230 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17229 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16062 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17157 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15948 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16064 (p : Pattern) (guard : d17231 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17231, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d17231, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17230 p = 1 := by simpa only [d17231, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16063 p hg
    simpa only [d17231, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16065 (p : Pattern) (guard : d17232 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17232, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d17232, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17231 p = 1 := by simpa only [d17232, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16064 p hg
    simpa only [d17232, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16066 (p : Pattern) (guard : d17233 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17156 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15947 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15954 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16067 (p : Pattern) (guard : d17234 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15948 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17233 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16066 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16068 (p : Pattern) (guard : d17235 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17235, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d17235, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17234 p = 1 := by simpa only [d17235, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16067 p hg
    simpa only [d17235, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16069 (p : Pattern) (guard : d17236 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17236, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d17236, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17235 p = 1 := by simpa only [d17236, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16068 p hg
    simpa only [d17236, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16070 (p : Pattern) (guard : d17237 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17232 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16065 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17236 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16069 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16071 (p : Pattern) (guard : d17238 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17237 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16070 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17168 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15969 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16072 (p : Pattern) (guard : d17239 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17238 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16071 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16073 (p : Pattern) (guard : d17240 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17239 p = 1 := by simpa only [d17240, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16072 p hg
    simpa only [d17240, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17240, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17240, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16074 (p : Pattern) (guard : d17241 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17241, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17241, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17240 p = 1 := by simpa only [d17241, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16073 p hg
    simpa only [d17241, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16075 (p : Pattern) (guard : d17242 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17167 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15968 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16076 (p : Pattern) (guard : d17243 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15969 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17242 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16075 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16077 (p : Pattern) (guard : d17244 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17243 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16076 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16078 (p : Pattern) (guard : d17245 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17244 p = 1 := by simpa only [d17245, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16077 p hg
    simpa only [d17245, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17245, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17245, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16079 (p : Pattern) (guard : d17246 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17246, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17246, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17245 p = 1 := by simpa only [d17246, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16078 p hg
    simpa only [d17246, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16080 (p : Pattern) (guard : d17247 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17241 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16074 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17246 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16079 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16081 (p : Pattern) (guard : d17248 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17247 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16080 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16082 (p : Pattern) (guard : d17249 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17248 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16081 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16083 (p : Pattern) (guard : d17250 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17249 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16082 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16084 (p : Pattern) (guard : d17251 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17246 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16079 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15985 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16085 (p : Pattern) (guard : d17252 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17251 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16084 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16086 (p : Pattern) (guard : d17253 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17252 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16085 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16087 (p : Pattern) (guard : d17254 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17253 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16086 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16088 (p : Pattern) (guard : d17255 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17250 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16083 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17254 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16087 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16089 (p : Pattern) (guard : d128396 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17255 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16088 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16090 (p : Pattern) (guard : d13614 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15972 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16091 (p : Pattern) (guard : d17294 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15955 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13614 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16090 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16092 (p : Pattern) (guard : d17295 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17295, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d17295, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17294 p = 1 := by simpa only [d17295, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16091 p hg
    simpa only [d17295, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16093 (p : Pattern) (guard : d17296 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17296, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d17296, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17295 p = 1 := by simpa only [d17296, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16092 p hg
    simpa only [d17296, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16094 (p : Pattern) (guard : d17297 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17296 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16093 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16095 (p : Pattern) (guard : d17298 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15969 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17297 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16094 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16096 (p : Pattern) (guard : d17299 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17298 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16095 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16097 (p : Pattern) (guard : d17300 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17299 p = 1 := by simpa only [d17300, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16096 p hg
    simpa only [d17300, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17300, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17300, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16098 (p : Pattern) (guard : d17301 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17301, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17301, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17300 p = 1 := by simpa only [d17301, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16097 p hg
    simpa only [d17301, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16099 (p : Pattern) (guard : d17302 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17301 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16098 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16100 (p : Pattern) (guard : d17303 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17302 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16099 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16101 (p : Pattern) (guard : d17304 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17303 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16100 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16102 (p : Pattern) (guard : d17305 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17304 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16101 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16103 (p : Pattern) (guard : d17306 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17305 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16102 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16104 (p : Pattern) (guard : d17307 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17306 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16103 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16105 (p : Pattern) (guard : d128397 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128396 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16089 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17307 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16104 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16106 (p : Pattern) (guard : d128398 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d17224 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16055 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128397 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16105 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16107 (p : Pattern) (guard : d128399 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d17215 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16046 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128398 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16106 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16108 (p : Pattern) (guard : d128400 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128399 p = 1 := by simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16107 p hg
    simpa only [d128400, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16109 (p : Pattern) (guard : d17208 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17182 p = 1 := by simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16016 p hg
    simpa only [d17208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16110 (p : Pattern) (guard : d17209 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17208 p = 1 := by simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16109 p hg
    simpa only [d17209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16111 (p : Pattern) (guard : d17210 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17186 p = 1 := by simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d17210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16112 (p : Pattern) (guard : d17211 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17210 p = 1 := by simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16111 p hg
    simpa only [d17211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16113 (p : Pattern) (guard : d17212 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17209 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16110 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17211 p = 1 := by simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d17212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16114 (p : Pattern) (guard : d17213 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17212 p = 1 := by simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16113 p hg
    simpa only [d17213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16115 (p : Pattern) (guard : d17214 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17213 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16114 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16116 (p : Pattern) (guard : d17215 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17214 p = 1 := by simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16115 p hg
    simpa only [d17215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16117 (p : Pattern) (guard : d17216 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17181 p = 1 := by simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16015 p hg
    simpa only [d17216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16118 (p : Pattern) (guard : d17217 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17216 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16117 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16119 (p : Pattern) (guard : d17218 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17217 p = 1 := by simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16118 p hg
    simpa only [d17218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16120 (p : Pattern) (guard : d17219 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17185 p = 1 := by simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16019 p hg
    simpa only [d17219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16121 (p : Pattern) (guard : d17220 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17219 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16120 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16122 (p : Pattern) (guard : d17221 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17220 p = 1 := by simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16121 p hg
    simpa only [d17221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16123 (p : Pattern) (guard : d17222 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17218 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16119 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17221 p = 1 := by simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16122 p hg
    simpa only [d17222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16124 (p : Pattern) (guard : d17223 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17222 p = 1 := by simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16123 p hg
    simpa only [d17223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16125 (p : Pattern) (guard : d17224 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17223 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16124 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16126 (p : Pattern) (guard : d17232 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17232, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d17232, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17231 p = 1 := by simpa only [d17232, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16064 p hg
    simpa only [d17232, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16127 (p : Pattern) (guard : d17236 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17236, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d17236, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17235 p = 1 := by simpa only [d17236, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16068 p hg
    simpa only [d17236, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16128 (p : Pattern) (guard : d17237 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17232 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16126 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17236 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16127 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16129 (p : Pattern) (guard : d17238 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17237 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16128 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17168 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16130 (p : Pattern) (guard : d17239 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17238 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16129 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16131 (p : Pattern) (guard : d17240 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17239 p = 1 := by simpa only [d17240, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16130 p hg
    simpa only [d17240, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17240, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17240, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16132 (p : Pattern) (guard : d17241 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17241, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d17241, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17240 p = 1 := by simpa only [d17241, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16131 p hg
    simpa only [d17241, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16133 (p : Pattern) (guard : d17242 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17167 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16003 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16134 (p : Pattern) (guard : d17243 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17242 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16133 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16135 (p : Pattern) (guard : d17244 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17243 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16134 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16136 (p : Pattern) (guard : d17245 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17244 p = 1 := by simpa only [d17245, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16135 p hg
    simpa only [d17245, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17245, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17245, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16137 (p : Pattern) (guard : d17246 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17246, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d17246, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17245 p = 1 := by simpa only [d17246, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16136 p hg
    simpa only [d17246, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16138 (p : Pattern) (guard : d17247 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17241 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16132 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17246 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16137 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16139 (p : Pattern) (guard : d17248 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17247 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16138 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16140 (p : Pattern) (guard : d17249 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17248 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16139 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16141 (p : Pattern) (guard : d17250 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17249 p = 1 := by simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16140 p hg
    simpa only [d17250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16142 (p : Pattern) (guard : d17251 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17246 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16137 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16014 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16143 (p : Pattern) (guard : d17252 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17251 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16142 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16144 (p : Pattern) (guard : d17253 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17252 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16143 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16145 (p : Pattern) (guard : d17254 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17253 p = 1 := by simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16144 p hg
    simpa only [d17254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16146 (p : Pattern) (guard : d17255 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17250 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16141 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17254 p = 1 := by simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16145 p hg
    simpa only [d17255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16147 (p : Pattern) (guard : d128396 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17255 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16146 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16148 (p : Pattern) (guard : d17296 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17296, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d17296, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17295 p = 1 := by simpa only [d17296, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16092 p hg
    simpa only [d17296, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16149 (p : Pattern) (guard : d17297 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17296 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16148 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16150 (p : Pattern) (guard : d17298 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17297 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16149 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16151 (p : Pattern) (guard : d17299 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17298 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16150 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16152 (p : Pattern) (guard : d17300 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17299 p = 1 := by simpa only [d17300, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d17300, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17300, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17300, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16153 (p : Pattern) (guard : d17301 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17301, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d17301, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17300 p = 1 := by simpa only [d17301, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16152 p hg
    simpa only [d17301, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16154 (p : Pattern) (guard : d17302 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17301 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16153 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16155 (p : Pattern) (guard : d17303 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17302 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16154 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16156 (p : Pattern) (guard : d17304 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17303 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16155 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16157 (p : Pattern) (guard : d17305 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17304 p = 1 := by simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16156 p hg
    simpa only [d17305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16158 (p : Pattern) (guard : d17306 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17305 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16157 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16159 (p : Pattern) (guard : d17307 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17306 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16158 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16160 (p : Pattern) (guard : d128397 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128396 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16147 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17307 p = 1 := by simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16159 p hg
    simpa only [d128397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16161 (p : Pattern) (guard : d128398 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d17224 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16125 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128397 p = 1 := by simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16160 p hg
    simpa only [d128398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16162 (p : Pattern) (guard : d128399 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d17215 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16116 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128398 p = 1 := by simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16161 p hg
    simpa only [d128399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16163 (p : Pattern) (guard : d17312 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17208 p = 1 := by simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16039 p hg
    simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16164 (p : Pattern) (guard : d17313 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17210 p = 1 := by simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16041 p hg
    simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16165 (p : Pattern) (guard : d17314 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17312 p = 1 := by simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16163 p hg
    simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17313 p = 1 := by simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16164 p hg
    simpa only [d17314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16166 (p : Pattern) (guard : d17315 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17314 p = 1 := by simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16165 p hg
    simpa only [d17315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16167 (p : Pattern) (guard : d17316 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17315 p = 1 := by simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16166 p hg
    simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16168 (p : Pattern) (guard : d17317 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17316 p = 1 := by simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16167 p hg
    simpa only [d17317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16169 (p : Pattern) (guard : d17318 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17217 p = 1 := by simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16048 p hg
    simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16170 (p : Pattern) (guard : d17319 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17220 p = 1 := by simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16051 p hg
    simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16171 (p : Pattern) (guard : d17320 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17318 p = 1 := by simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16169 p hg
    simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17319 p = 1 := by simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16170 p hg
    simpa only [d17320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16172 (p : Pattern) (guard : d17321 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17320 p = 1 := by simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16171 p hg
    simpa only [d17321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16173 (p : Pattern) (guard : d17322 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17321 p = 1 := by simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16172 p hg
    simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16174 (p : Pattern) (guard : d17323 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17249 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16082 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16175 (p : Pattern) (guard : d17324 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17253 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16086 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16176 (p : Pattern) (guard : d17325 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17323 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16174 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17324 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16175 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16177 (p : Pattern) (guard : d128401 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17325 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16176 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16178 (p : Pattern) (guard : d17330 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17304 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16101 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16179 (p : Pattern) (guard : d17331 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17330 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16178 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16180 (p : Pattern) (guard : d17332 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17331 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16179 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16181 (p : Pattern) (guard : d128402 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128401 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16177 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17332 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16180 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16182 (p : Pattern) (guard : d128403 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d17322 p = 1 := by simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16173 p hg
    simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128402 p = 1 := by simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16181 p hg
    simpa only [d128403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16183 (p : Pattern) (guard : d128404 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d17317 p = 1 := by simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16168 p hg
    simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128403 p = 1 := by simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16182 p hg
    simpa only [d128404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16184 (p : Pattern) (guard : d128405 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128399 p = 1 := by simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16162 p hg
    simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128404 p = 1 := by simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16183 p hg
    simpa only [d128405, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16185 (p : Pattern) (guard : d128406 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128400 p = 1 := by simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16108 p hg
    simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128405 p = 1 := by simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16184 p hg
    simpa only [d128406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16186 (p : Pattern) (guard : d17338 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17254 p = 1 := by simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16145 p hg
    simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16022 p hg
    simpa only [d17338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16187 (p : Pattern) (guard : d17339 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17338 p = 1 := by simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16186 p hg
    simpa only [d17339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16188 (p : Pattern) (guard : d17340 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17339 p = 1 := by simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16187 p hg
    simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16189 (p : Pattern) (guard : d17341 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17340 p = 1 := by simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16188 p hg
    simpa only [d17341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16190 (p : Pattern) (guard : d17342 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17341 p = 1 := by simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16189 p hg
    simpa only [d17342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16191 (p : Pattern) (guard : d17343 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17188 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15993 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16192 (p : Pattern) (guard : d17344 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17343 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16191 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16193 (p : Pattern) (guard : d17345 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17344 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16192 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16194 (p : Pattern) (guard : d17346 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17345 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16193 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16195 (p : Pattern) (guard : d17347 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17346 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16194 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16196 (p : Pattern) (guard : d17348 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17342 p = 1 := by simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16190 p hg
    simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17347 p = 1 := by simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16195 p hg
    simpa only [d17348, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16197 (p : Pattern) (guard : d17343 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17188 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16022 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16198 (p : Pattern) (guard : d17344 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17343 p = 1 := by simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16197 p hg
    simpa only [d17344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16199 (p : Pattern) (guard : d17345 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17344 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16198 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16200 (p : Pattern) (guard : d17346 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17345 p = 1 := by simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16199 p hg
    simpa only [d17346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16201 (p : Pattern) (guard : d17347 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17346 p = 1 := by simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16200 p hg
    simpa only [d17347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16202 (p : Pattern) (guard : d17349 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17198 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16029 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16203 (p : Pattern) (guard : d17350 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17349 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16202 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16204 (p : Pattern) (guard : d17351 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17350 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16203 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16205 (p : Pattern) (guard : d17352 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17351 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16204 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16206 (p : Pattern) (guard : d17353 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17352 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16205 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16207 (p : Pattern) (guard : d17354 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17347 p = 1 := by simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16201 p hg
    simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17353 p = 1 := by simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16206 p hg
    simpa only [d17354, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16208 (p : Pattern) (guard : d17355 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d17348 p = 1 := by simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16196 p hg
    simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17354 p = 1 := by simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16207 p hg
    simpa only [d17355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16209 (p : Pattern) (guard : d128407 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128406 p = 1 := by simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16185 p hg
    simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17355 p = 1 := by simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16208 p hg
    simpa only [d128407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16210 (p : Pattern) (guard : d128408 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128407 p = 1 := by simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16209 p hg
    simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d128408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16211 (p : Pattern) (guard : d128409 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d17207 p = 1 := by simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16038 p hg
    simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128408 p = 1 := by simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16210 p hg
    simpa only [d128409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16212 (p : Pattern) (guard : d2146 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16213 (p : Pattern) (guard : d2147 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16212 p hg
    simpa only [d2147, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d2147, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16214 (p : Pattern) (guard : d17225 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16215 (p : Pattern) (guard : d17226 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16214 p hg
    simpa only [d17226, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d17226, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16216 (p : Pattern) (guard : d17227 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16213 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16215 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16217 (p : Pattern) (guard : d13675 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16218 (p : Pattern) (guard : d13676 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16217 p hg
    simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16219 (p : Pattern) (guard : d17228 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13676 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16218 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16220 (p : Pattern) (guard : d17229 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17227 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16216 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17228 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16219 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16221 (p : Pattern) (guard : d2037 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16222 (p : Pattern) (guard : d2038 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16221 p hg
    simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16223 (p : Pattern) (guard : d17153 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16224 (p : Pattern) (guard : d17154 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16223 p hg
    simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16225 (p : Pattern) (guard : d17155 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16222 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16224 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16226 (p : Pattern) (guard : d15548 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16227 (p : Pattern) (guard : d15549 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16226 p hg
    simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16228 (p : Pattern) (guard : d17156 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16218 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16227 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16229 (p : Pattern) (guard : d17157 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16225 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16228 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16230 (p : Pattern) (guard : d17230 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17229 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16220 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17157 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16229 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16231 (p : Pattern) (guard : d17231 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17231, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d17231, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17230 p = 1 := by simpa only [d17231, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16230 p hg
    simpa only [d17231, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16232 (p : Pattern) (guard : d17232 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17232, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d17232, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17231 p = 1 := by simpa only [d17232, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16231 p hg
    simpa only [d17232, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16233 (p : Pattern) (guard : d15550 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16227 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16234 (p : Pattern) (guard : d17233 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17156 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16228 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16233 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16235 (p : Pattern) (guard : d17234 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16229 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17233 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16234 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16236 (p : Pattern) (guard : d17235 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17235, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d17235, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17234 p = 1 := by simpa only [d17235, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16235 p hg
    simpa only [d17235, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16237 (p : Pattern) (guard : d17236 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17236, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d17236, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17235 p = 1 := by simpa only [d17236, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16236 p hg
    simpa only [d17236, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16238 (p : Pattern) (guard : d17237 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17232 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16232 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17236 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16237 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16239 (p : Pattern) (guard : d2055 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16240 (p : Pattern) (guard : d2056 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16239 p hg
    simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16241 (p : Pattern) (guard : d17158 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16242 (p : Pattern) (guard : d17159 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16241 p hg
    simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16243 (p : Pattern) (guard : d17160 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16240 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16242 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16244 (p : Pattern) (guard : d17161 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16243 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16233 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16245 (p : Pattern) (guard : d17162 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16229 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16244 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16246 (p : Pattern) (guard : d17163 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16245 p hg
    simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16247 (p : Pattern) (guard : d17164 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16246 p hg
    simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16248 (p : Pattern) (guard : d5249 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16249 (p : Pattern) (guard : d5250 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16248 p hg
    simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
