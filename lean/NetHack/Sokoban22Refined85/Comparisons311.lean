/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons310
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43540 (p : Pattern) (guard : d8098 p = 1) : d1509 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43535 p hg
    simpa only [d8098, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43539 p hg
    simpa only [d8098, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43541 (p : Pattern) (guard : d8091 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare43542 (p : Pattern) (guard : d8092 p = 1) : d46 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34375 p hg
    simpa only [d8092, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43541 p hg
    simpa only [d8092, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43543 (p : Pattern) (guard : d8096 p = 1) : d43 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34383 p hg
    simpa only [d8096, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43544 (p : Pattern) (guard : d8097 p = 1) : d47 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43542 p hg
    simpa only [d8097, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43543 p hg
    simpa only [d8097, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43545 (p : Pattern) (guard : d8096 p = 1) : d48 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34396 p hg
    simpa only [d8096, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43546 (p : Pattern) (guard : d8102 p = 1) : d49 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43545 p hg
    simpa only [d8102, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43547 (p : Pattern) (guard : d8103 p = 1) : d50 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43544 p hg
    simpa only [d8103, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43546 p hg
    simpa only [d8103, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43548 (p : Pattern) (guard : d8104 p = 1) : d1510 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43540 p hg
    simpa only [d8104, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43547 p hg
    simpa only [d8104, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43549 (p : Pattern) (guard : d8092 p = 1) : d46 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34406 p hg
    simpa only [d8092, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43541 p hg
    simpa only [d8092, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43550 (p : Pattern) (guard : d8096 p = 1) : d46 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34419 p hg
    simpa only [d8096, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43551 (p : Pattern) (guard : d8097 p = 1) : d46 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43549 p hg
    simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43550 p hg
    simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43552 (p : Pattern) (guard : d8096 p = 1) : d46 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34430 p hg
    simpa only [d8096, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43553 (p : Pattern) (guard : d8102 p = 1) : d47 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43552 p hg
    simpa only [d8102, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34444 p hg
    simpa only [d8102, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43554 (p : Pattern) (guard : d8103 p = 1) : d1511 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43551 p hg
    simpa only [d8103, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43553 p hg
    simpa only [d8103, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43555 (p : Pattern) (guard : d8109 p = 1) : d1512 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43554 p hg
    simpa only [d8109, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34457 p hg
    simpa only [d8109, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43556 (p : Pattern) (guard : d8110 p = 1) : d1513 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43548 p hg
    simpa only [d8110, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43555 p hg
    simpa only [d8110, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43557 (p : Pattern) (guard : d8091 p = 1) : d359 p ≤ (0 : Int) + d359 p := by
  omega
theorem compare43558 (p : Pattern) (guard : d8092 p = 1) : d1514 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34464 p hg
    simpa only [d8092, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43557 p hg
    simpa only [d8092, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43559 (p : Pattern) (guard : d8096 p = 1) : d66 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34475 p hg
    simpa only [d8096, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43560 (p : Pattern) (guard : d8097 p = 1) : d1515 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43558 p hg
    simpa only [d8097, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43559 p hg
    simpa only [d8097, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43561 (p : Pattern) (guard : d8096 p = 1) : d43 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34483 p hg
    simpa only [d8096, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43562 (p : Pattern) (guard : d8101 p = 1) : d48 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34487 p hg
    simpa only [d8101, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43563 (p : Pattern) (guard : d8102 p = 1) : d68 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43561 p hg
    simpa only [d8102, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43562 p hg
    simpa only [d8102, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43564 (p : Pattern) (guard : d8103 p = 1) : d1516 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43560 p hg
    simpa only [d8103, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43563 p hg
    simpa only [d8103, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43565 (p : Pattern) (guard : d8101 p = 1) : d70 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34503 p hg
    simpa only [d8101, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43566 (p : Pattern) (guard : d8102 p = 1) : d71 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43538 p hg
    simpa only [d8102, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43565 p hg
    simpa only [d8102, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43567 (p : Pattern) (guard : d8101 p = 1) : d72 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34512 p hg
    simpa only [d8101, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43568 (p : Pattern) (guard : d8107 p = 1) : d73 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43567 p hg
    simpa only [d8107, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43569 (p : Pattern) (guard : d8108 p = 1) : d74 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43566 p hg
    simpa only [d8108, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43568 p hg
    simpa only [d8108, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43570 (p : Pattern) (guard : d8109 p = 1) : d1517 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43564 p hg
    simpa only [d8109, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43569 p hg
    simpa only [d8109, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43571 (p : Pattern) (guard : d8096 p = 1) : d46 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34519 p hg
    simpa only [d8096, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43572 (p : Pattern) (guard : d8102 p = 1) : d1518 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43571 p hg
    simpa only [d8102, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34528 p hg
    simpa only [d8102, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43573 (p : Pattern) (guard : d8108 p = 1) : d1519 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43572 p hg
    simpa only [d8108, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34534 p hg
    simpa only [d8108, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43574 (p : Pattern) (guard : d8114 p = 1) : d1520 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43573 p hg
    simpa only [d8114, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34545 p hg
    simpa only [d8114, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43575 (p : Pattern) (guard : d8115 p = 1) : d1521 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43570 p hg
    simpa only [d8115, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43574 p hg
    simpa only [d8115, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43576 (p : Pattern) (guard : d8116 p = 1) : d1522 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43556 p hg
    simpa only [d8116, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43575 p hg
    simpa only [d8116, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43577 (p : Pattern) (guard : d8097 p = 1) : d46 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43542 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43571 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43578 (p : Pattern) (guard : d8102 p = 1) : d47 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43550 p hg
    simpa only [d8102, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34444 p hg
    simpa only [d8102, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43579 (p : Pattern) (guard : d8103 p = 1) : d1511 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43577 p hg
    simpa only [d8103, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43578 p hg
    simpa only [d8103, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43580 (p : Pattern) (guard : d8108 p = 1) : d50 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43553 p hg
    simpa only [d8108, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34456 p hg
    simpa only [d8108, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43581 (p : Pattern) (guard : d8109 p = 1) : d1512 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43579 p hg
    simpa only [d8109, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43580 p hg
    simpa only [d8109, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43582 (p : Pattern) (guard : d8096 p = 1) : d66 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34565 p hg
    simpa only [d8096, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43583 (p : Pattern) (guard : d8101 p = 1) : d173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34569 p hg
    simpa only [d8101, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43584 (p : Pattern) (guard : d8102 p = 1) : d176 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43582 p hg
    simpa only [d8102, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43583 p hg
    simpa only [d8102, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43585 (p : Pattern) (guard : d8101 p = 1) : d72 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34573 p hg
    simpa only [d8101, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43586 (p : Pattern) (guard : d8107 p = 1) : d73 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43585 p hg
    simpa only [d8107, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43587 (p : Pattern) (guard : d8108 p = 1) : d177 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43584 p hg
    simpa only [d8108, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43586 p hg
    simpa only [d8108, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43588 (p : Pattern) (guard : d8114 p = 1) : d1523 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43587 p hg
    simpa only [d8114, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43589 (p : Pattern) (guard : d8115 p = 1) : d1524 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43581 p hg
    simpa only [d8115, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43588 p hg
    simpa only [d8115, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43590 (p : Pattern) (guard : d8096 p = 1) : d46 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34581 p hg
    simpa only [d8096, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43591 (p : Pattern) (guard : d8101 p = 1) : d66 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34588 p hg
    simpa only [d8101, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43592 (p : Pattern) (guard : d8102 p = 1) : d1518 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43590 p hg
    simpa only [d8102, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43591 p hg
    simpa only [d8102, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43593 (p : Pattern) (guard : d8101 p = 1) : d43 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34596 p hg
    simpa only [d8101, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43594 (p : Pattern) (guard : d8107 p = 1) : d68 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43593 p hg
    simpa only [d8107, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34533 p hg
    simpa only [d8107, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43595 (p : Pattern) (guard : d8108 p = 1) : d1519 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43592 p hg
    simpa only [d8108, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43594 p hg
    simpa only [d8108, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43596 (p : Pattern) (guard : d8114 p = 1) : d1520 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43595 p hg
    simpa only [d8114, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34545 p hg
    simpa only [d8114, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43597 (p : Pattern) (guard : d8107 p = 1) : d183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43583 p hg
    simpa only [d8107, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43598 (p : Pattern) (guard : d8113 p = 1) : d184 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43597 p hg
    simpa only [d8113, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43599 (p : Pattern) (guard : d8119 p = 1) : d1525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43598 p hg
    simpa only [d8119, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43600 (p : Pattern) (guard : d8120 p = 1) : d1526 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43596 p hg
    simpa only [d8120, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43599 p hg
    simpa only [d8120, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43601 (p : Pattern) (guard : d8121 p = 1) : d1527 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43589 p hg
    simpa only [d8121, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43600 p hg
    simpa only [d8121, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43602 (p : Pattern) (guard : d8122 p = 1) : d1528 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43576 p hg
    simpa only [d8122, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43601 p hg
    simpa only [d8122, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43603 (p : Pattern) (guard : d8097 p = 1) : d1529 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43537 p hg
    simpa only [d8097, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43590 p hg
    simpa only [d8097, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43604 (p : Pattern) (guard : d8102 p = 1) : d47 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43571 p hg
    simpa only [d8102, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43593 p hg
    simpa only [d8102, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43605 (p : Pattern) (guard : d8103 p = 1) : d1530 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43603 p hg
    simpa only [d8103, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43604 p hg
    simpa only [d8103, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43606 (p : Pattern) (guard : d8108 p = 1) : d50 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43578 p hg
    simpa only [d8108, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34456 p hg
    simpa only [d8108, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43607 (p : Pattern) (guard : d8109 p = 1) : d1531 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43605 p hg
    simpa only [d8109, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43606 p hg
    simpa only [d8109, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43608 (p : Pattern) (guard : d8096 p = 1) : d66 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38109 p hg
    simpa only [d8096, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43609 (p : Pattern) (guard : d8102 p = 1) : d176 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43608 p hg
    simpa only [d8102, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43583 p hg
    simpa only [d8102, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43610 (p : Pattern) (guard : d8108 p = 1) : d177 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43609 p hg
    simpa only [d8108, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43586 p hg
    simpa only [d8108, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43611 (p : Pattern) (guard : d8114 p = 1) : d1523 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43610 p hg
    simpa only [d8114, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43612 (p : Pattern) (guard : d8115 p = 1) : d1532 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43607 p hg
    simpa only [d8115, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43611 p hg
    simpa only [d8115, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43613 (p : Pattern) (guard : d8096 p = 1) : d46 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34621 p hg
    simpa only [d8096, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43614 (p : Pattern) (guard : d8101 p = 1) : d66 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41376 p hg
    simpa only [d8101, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43615 (p : Pattern) (guard : d8102 p = 1) : d1518 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43613 p hg
    simpa only [d8102, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43614 p hg
    simpa only [d8102, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43616 (p : Pattern) (guard : d8101 p = 1) : d43 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34628 p hg
    simpa only [d8101, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43617 (p : Pattern) (guard : d8107 p = 1) : d68 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43616 p hg
    simpa only [d8107, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34533 p hg
    simpa only [d8107, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43618 (p : Pattern) (guard : d8108 p = 1) : d1519 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43615 p hg
    simpa only [d8108, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43617 p hg
    simpa only [d8108, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43619 (p : Pattern) (guard : d8107 p = 1) : d71 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43593 p hg
    simpa only [d8107, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34538 p hg
    simpa only [d8107, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43620 (p : Pattern) (guard : d8113 p = 1) : d74 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43619 p hg
    simpa only [d8113, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43621 (p : Pattern) (guard : d8114 p = 1) : d1520 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43618 p hg
    simpa only [d8114, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43620 p hg
    simpa only [d8114, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43622 (p : Pattern) (guard : d8120 p = 1) : d1526 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43621 p hg
    simpa only [d8120, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43599 p hg
    simpa only [d8120, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43623 (p : Pattern) (guard : d8121 p = 1) : d1533 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43612 p hg
    simpa only [d8121, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43622 p hg
    simpa only [d8121, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43624 (p : Pattern) (guard : d8102 p = 1) : d1534 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43545 p hg
    simpa only [d8102, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43585 p hg
    simpa only [d8102, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43625 (p : Pattern) (guard : d8108 p = 1) : d1535 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43624 p hg
    simpa only [d8108, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43586 p hg
    simpa only [d8108, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43626 (p : Pattern) (guard : d8113 p = 1) : d1536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43586 p hg
    simpa only [d8113, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43627 (p : Pattern) (guard : d8114 p = 1) : d1537 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43625 p hg
    simpa only [d8114, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43626 p hg
    simpa only [d8114, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43628 (p : Pattern) (guard : d8119 p = 1) : d1538 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43626 p hg
    simpa only [d8119, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43629 (p : Pattern) (guard : d8120 p = 1) : d1539 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43627 p hg
    simpa only [d8120, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43628 p hg
    simpa only [d8120, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43630 (p : Pattern) (guard : d8113 p = 1) : d1536 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43568 p hg
    simpa only [d8113, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43631 (p : Pattern) (guard : d8119 p = 1) : d1538 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43630 p hg
    simpa only [d8119, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43632 (p : Pattern) (guard : d8125 p = 1) : d1540 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43631 p hg
    simpa only [d8125, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43633 (p : Pattern) (guard : d8126 p = 1) : d1541 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43629 p hg
    simpa only [d8126, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43632 p hg
    simpa only [d8126, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43634 (p : Pattern) (guard : d8127 p = 1) : d1542 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43623 p hg
    simpa only [d8127, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43633 p hg
    simpa only [d8127, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43635 (p : Pattern) (guard : d8128 p = 1) : d1543 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43602 p hg
    simpa only [d8128, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43634 p hg
    simpa only [d8128, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43636 (p : Pattern) (guard : d8097 p = 1) : d1544 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43534 p hg
    simpa only [d8097, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43613 p hg
    simpa only [d8097, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43637 (p : Pattern) (guard : d8102 p = 1) : d47 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43590 p hg
    simpa only [d8102, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43616 p hg
    simpa only [d8102, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43638 (p : Pattern) (guard : d8103 p = 1) : d1545 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43636 p hg
    simpa only [d8103, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43637 p hg
    simpa only [d8103, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43639 (p : Pattern) (guard : d8108 p = 1) : d50 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43604 p hg
    simpa only [d8108, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34456 p hg
    simpa only [d8108, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43640 (p : Pattern) (guard : d8109 p = 1) : d1546 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43638 p hg
    simpa only [d8109, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43639 p hg
    simpa only [d8109, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43641 (p : Pattern) (guard : d8102 p = 1) : d46 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43550 p hg
    simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34647 p hg
    simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43642 (p : Pattern) (guard : d8108 p = 1) : d1511 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43641 p hg
    simpa only [d8108, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34648 p hg
    simpa only [d8108, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43643 (p : Pattern) (guard : d8114 p = 1) : d1512 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43642 p hg
    simpa only [d8114, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d8114, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43644 (p : Pattern) (guard : d8115 p = 1) : d1547 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43640 p hg
    simpa only [d8115, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43643 p hg
    simpa only [d8115, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43645 (p : Pattern) (guard : d8096 p = 1) : d46 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34654 p hg
    simpa only [d8096, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43646 (p : Pattern) (guard : d8101 p = 1) : d66 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34660 p hg
    simpa only [d8101, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43647 (p : Pattern) (guard : d8102 p = 1) : d1518 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43645 p hg
    simpa only [d8102, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43646 p hg
    simpa only [d8102, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43648 (p : Pattern) (guard : d8101 p = 1) : d43 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34667 p hg
    simpa only [d8101, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43649 (p : Pattern) (guard : d8107 p = 1) : d68 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43648 p hg
    simpa only [d8107, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34533 p hg
    simpa only [d8107, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43650 (p : Pattern) (guard : d8108 p = 1) : d1519 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43647 p hg
    simpa only [d8108, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43649 p hg
    simpa only [d8108, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43651 (p : Pattern) (guard : d8107 p = 1) : d71 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43616 p hg
    simpa only [d8107, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34538 p hg
    simpa only [d8107, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43652 (p : Pattern) (guard : d8113 p = 1) : d74 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43651 p hg
    simpa only [d8113, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43653 (p : Pattern) (guard : d8114 p = 1) : d1520 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43650 p hg
    simpa only [d8114, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43652 p hg
    simpa only [d8114, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43654 (p : Pattern) (guard : d8107 p = 1) : d1518 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34960 p hg
    simpa only [d8107, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d8107, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43655 (p : Pattern) (guard : d8113 p = 1) : d1519 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43654 p hg
    simpa only [d8113, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d8113, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43656 (p : Pattern) (guard : d8119 p = 1) : d1520 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43655 p hg
    simpa only [d8119, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43657 (p : Pattern) (guard : d8120 p = 1) : d1520 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43653 p hg
    simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43656 p hg
    simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43658 (p : Pattern) (guard : d8121 p = 1) : d1548 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43644 p hg
    simpa only [d8121, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43657 p hg
    simpa only [d8121, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43659 (p : Pattern) (guard : d8102 p = 1) : d46 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43571 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34960 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43660 (p : Pattern) (guard : d8108 p = 1) : d1511 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43659 p hg
    simpa only [d8108, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34648 p hg
    simpa only [d8108, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43661 (p : Pattern) (guard : d8114 p = 1) : d1512 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43660 p hg
    simpa only [d8114, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d8114, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43662 (p : Pattern) (guard : d8101 p = 1) : d66 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34707 p hg
    simpa only [d8101, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43663 (p : Pattern) (guard : d8106 p = 1) : d173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34710 p hg
    simpa only [d8106, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43664 (p : Pattern) (guard : d8107 p = 1) : d176 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43662 p hg
    simpa only [d8107, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43663 p hg
    simpa only [d8107, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43665 (p : Pattern) (guard : d8113 p = 1) : d177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43664 p hg
    simpa only [d8113, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43666 (p : Pattern) (guard : d8119 p = 1) : d1523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43665 p hg
    simpa only [d8119, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43667 (p : Pattern) (guard : d8120 p = 1) : d1524 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43661 p hg
    simpa only [d8120, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43666 p hg
    simpa only [d8120, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43668 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34719 p hg
    simpa only [d8101, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43669 (p : Pattern) (guard : d8107 p = 1) : d1518 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43668 p hg
    simpa only [d8107, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d8107, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43670 (p : Pattern) (guard : d8113 p = 1) : d1519 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43669 p hg
    simpa only [d8113, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d8113, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43671 (p : Pattern) (guard : d8119 p = 1) : d1520 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43670 p hg
    simpa only [d8119, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43672 (p : Pattern) (guard : d8112 p = 1) : d183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43663 p hg
    simpa only [d8112, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43673 (p : Pattern) (guard : d8118 p = 1) : d184 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43672 p hg
    simpa only [d8118, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43674 (p : Pattern) (guard : d8124 p = 1) : d1525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43673 p hg
    simpa only [d8124, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43675 (p : Pattern) (guard : d8125 p = 1) : d1526 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43671 p hg
    simpa only [d8125, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43674 p hg
    simpa only [d8125, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43676 (p : Pattern) (guard : d8126 p = 1) : d1527 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43667 p hg
    simpa only [d8126, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43675 p hg
    simpa only [d8126, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43677 (p : Pattern) (guard : d8127 p = 1) : d1549 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43658 p hg
    simpa only [d8127, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43676 p hg
    simpa only [d8127, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43678 (p : Pattern) (guard : d8102 p = 1) : d46 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43590 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43668 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43679 (p : Pattern) (guard : d8108 p = 1) : d1511 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43678 p hg
    simpa only [d8108, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d8108, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
