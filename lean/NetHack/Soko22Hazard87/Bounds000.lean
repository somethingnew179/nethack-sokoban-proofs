import NetHack.Soko22Hazard87.CompareBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem bounds0 (p : Pattern) : (0 : Int) ≤ d0 p ∧ d0 p ≤ 0 := by
  change (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 0; decide
theorem bounds2 (p : Pattern) : (2 : Int) ≤ d2 p ∧ d2 p ≤ 2 := by
  change (2 : Int) ≤ 2 ∧ (2 : Int) ≤ 2; decide
theorem bounds3 (p : Pattern) : (3 : Int) ≤ d3 p ∧ d3 p ≤ 3 := by
  change (3 : Int) ≤ 3 ∧ (3 : Int) ≤ 3; decide
theorem bounds4 (p : Pattern) : (4 : Int) ≤ d4 p ∧ d4 p ≤ 4 := by
  change (4 : Int) ≤ 4 ∧ (4 : Int) ≤ 4; decide
theorem bounds5 (p : Pattern) : (5 : Int) ≤ d5 p ∧ d5 p ≤ 5 := by
  change (5 : Int) ≤ 5 ∧ (5 : Int) ≤ 5; decide
theorem bounds6 (p : Pattern) : (6 : Int) ≤ d6 p ∧ d6 p ≤ 6 := by
  change (6 : Int) ≤ 6 ∧ (6 : Int) ≤ 6; decide
theorem bounds8 (p : Pattern) : (8 : Int) ≤ d8 p ∧ d8 p ≤ 8 := by
  change (8 : Int) ≤ 8 ∧ (8 : Int) ≤ 8; decide
theorem bounds9 (p : Pattern) : (9 : Int) ≤ d9 p ∧ d9 p ≤ 9 := by
  change (9 : Int) ≤ 9 ∧ (9 : Int) ≤ 9; decide
theorem bounds10 (p : Pattern) : (10 : Int) ≤ d10 p ∧ d10 p ≤ 10 := by
  change (10 : Int) ≤ 10 ∧ (10 : Int) ≤ 10; decide
theorem bounds11 (p : Pattern) : (11 : Int) ≤ d11 p ∧ d11 p ≤ 11 := by
  change (11 : Int) ≤ 11 ∧ (11 : Int) ≤ 11; decide
theorem bounds12 (p : Pattern) : (12 : Int) ≤ d12 p ∧ d12 p ≤ 12 := by
  change (12 : Int) ≤ 12 ∧ (12 : Int) ≤ 12; decide
theorem bounds47616 (p : Pattern) : (4 : Int) ≤ d47616 p ∧ d47616 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d4 p) _ _ _ _ (bounds12 p) (bounds4 p)
theorem bounds47622 (p : Pattern) : (9 : Int) ≤ d47622 p ∧ d47622 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d9 p) _ _ _ _ (bounds12 p) (bounds9 p)
theorem bounds47629 (p : Pattern) : (2 : Int) ≤ d47629 p ∧ d47629 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d2 p) _ _ _ _ (bounds12 p) (bounds2 p)
theorem bounds47633 (p : Pattern) : (6 : Int) ≤ d47633 p ∧ d47633 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d6 p) _ _ _ _ (bounds12 p) (bounds6 p)
theorem bounds47638 (p : Pattern) : (11 : Int) ≤ d47638 p ∧ d47638 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d11 p) _ _ _ _ (bounds12 p) (bounds11 p)
theorem bounds47656 (p : Pattern) : (10 : Int) ≤ d47656 p ∧ d47656 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d10 p) _ _ _ _ (bounds12 p) (bounds10 p)
theorem bounds47705 (p : Pattern) : (5 : Int) ≤ d47705 p ∧ d47705 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d5 p) _ _ _ _ (bounds12 p) (bounds5 p)
theorem bounds47789 (p : Pattern) : (8 : Int) ≤ d47789 p ∧ d47789 p ≤ 12 := by
  exact integer_range_ite (p 247) (d12 p) (d8 p) _ _ _ _ (bounds12 p) (bounds8 p)
theorem bounds47926 (p : Pattern) : (11 : Int) ≤ d47926 p ∧ d47926 p ≤ 12 := by
  exact integer_range_ite (p 246) (d12 p) (d47638 p) _ _ _ _ (bounds12 p) (bounds47638 p)
theorem bounds47928 (p : Pattern) : (10 : Int) ≤ d47928 p ∧ d47928 p ≤ 12 := by
  exact integer_range_ite (p 246) (d12 p) (d47656 p) _ _ _ _ (bounds12 p) (bounds47656 p)
theorem bounds47938 (p : Pattern) : (4 : Int) ≤ d47938 p ∧ d47938 p ≤ 12 := by
  exact integer_range_ite (p 246) (d12 p) (d47616 p) _ _ _ _ (bounds12 p) (bounds47616 p)
theorem bounds47947 (p : Pattern) : (5 : Int) ≤ d47947 p ∧ d47947 p ≤ 12 := by
  exact integer_range_ite (p 246) (d12 p) (d47705 p) _ _ _ _ (bounds12 p) (bounds47705 p)
theorem bounds47963 (p : Pattern) : (6 : Int) ≤ d47963 p ∧ d47963 p ≤ 12 := by
  exact integer_range_ite (p 246) (d12 p) (d47633 p) _ _ _ _ (bounds12 p) (bounds47633 p)
theorem bounds49309 (p : Pattern) : (2 : Int) ≤ d49309 p ∧ d49309 p ≤ 8 := by
  exact integer_range_ite (p 247) (d8 p) (d2 p) _ _ _ _ (bounds8 p) (bounds2 p)
theorem bounds49312 (p : Pattern) : (2 : Int) ≤ d49312 p ∧ d49312 p ≤ 6 := by
  exact integer_range_ite (p 247) (d6 p) (d2 p) _ _ _ _ (bounds6 p) (bounds2 p)
theorem bounds49320 (p : Pattern) : (6 : Int) ≤ d49320 p ∧ d49320 p ≤ 10 := by
  exact integer_range_ite (p 247) (d10 p) (d6 p) _ _ _ _ (bounds10 p) (bounds6 p)
theorem bounds49390 (p : Pattern) : (4 : Int) ≤ d49390 p ∧ d49390 p ≤ 10 := by
  exact integer_range_ite (p 247) (d10 p) (d4 p) _ _ _ _ (bounds10 p) (bounds4 p)
theorem bounds49393 (p : Pattern) : (4 : Int) ≤ d49393 p ∧ d49393 p ≤ 8 := by
  exact integer_range_ite (p 247) (d8 p) (d4 p) _ _ _ _ (bounds8 p) (bounds4 p)
theorem bounds49559 (p : Pattern) : (5 : Int) ≤ d49559 p ∧ d49559 p ≤ 11 := by
  exact integer_range_ite (p 247) (d11 p) (d5 p) _ _ _ _ (bounds11 p) (bounds5 p)
theorem bounds49562 (p : Pattern) : (5 : Int) ≤ d49562 p ∧ d49562 p ≤ 9 := by
  exact integer_range_ite (p 247) (d9 p) (d5 p) _ _ _ _ (bounds9 p) (bounds5 p)
theorem bounds51154 (p : Pattern) : (4 : Int) ≤ d51154 p ∧ d51154 p ≤ 12 := by
  exact integer_range_ite (p 246) (d47789 p) (d47616 p) _ _ _ _ (bounds47789 p) (bounds47616 p)
theorem bounds51189 (p : Pattern) : (6 : Int) ≤ d51189 p ∧ d51189 p ≤ 12 := by
  exact integer_range_ite (p 225) (d47963 p) (d47633 p) _ _ _ _ (bounds47963 p) (bounds47633 p)
theorem bounds51190 (p : Pattern) : (6 : Int) ≤ d51190 p ∧ d51190 p ≤ 12 := by
  exact integer_range_ite (p 246) (d47656 p) (d47633 p) _ _ _ _ (bounds47656 p) (bounds47633 p)
theorem bounds51191 (p : Pattern) : (6 : Int) ≤ d51191 p ∧ d51191 p ≤ 12 := by
  exact integer_range_ite (p 225) (d47963 p) (d51190 p) _ _ _ _ (bounds47963 p) (bounds51190 p)
theorem bounds51192 (p : Pattern) : (6 : Int) ≤ d51192 p ∧ d51192 p ≤ 12 := by
  exact integer_range_ite (p 224) (d51191 p) (d51189 p) _ _ _ _ (bounds51191 p) (bounds51189 p)
theorem bounds51193 (p : Pattern) : (6 : Int) ≤ d51193 p ∧ d51193 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d51192 p) _ _ _ _ (bounds12 p) (bounds51192 p)
theorem bounds51196 (p : Pattern) : (11 : Int) ≤ d51196 p ∧ d51196 p ≤ 12 := by
  exact integer_range_ite (p 225) (d47926 p) (d47638 p) _ _ _ _ (bounds47926 p) (bounds47638 p)
theorem bounds51197 (p : Pattern) : (11 : Int) ≤ d51197 p ∧ d51197 p ≤ 12 := by
  exact integer_range_ite (p 224) (d47926 p) (d51196 p) _ _ _ _ (bounds47926 p) (bounds51196 p)
theorem bounds51198 (p : Pattern) : (11 : Int) ≤ d51198 p ∧ d51198 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d51197 p) _ _ _ _ (bounds12 p) (bounds51197 p)
theorem bounds51200 (p : Pattern) : (4 : Int) ≤ d51200 p ∧ d51200 p ≤ 12 := by
  exact integer_range_ite (p 246) (d47656 p) (d47616 p) _ _ _ _ (bounds47656 p) (bounds47616 p)
theorem bounds51201 (p : Pattern) : (4 : Int) ≤ d51201 p ∧ d51201 p ≤ 12 := by
  exact integer_range_ite (p 225) (d51200 p) (d47616 p) _ _ _ _ (bounds51200 p) (bounds47616 p)
theorem bounds51202 (p : Pattern) : (4 : Int) ≤ d51202 p ∧ d51202 p ≤ 12 := by
  exact integer_range_ite (p 225) (d47938 p) (d51154 p) _ _ _ _ (bounds47938 p) (bounds51154 p)
theorem bounds51203 (p : Pattern) : (4 : Int) ≤ d51203 p ∧ d51203 p ≤ 12 := by
  exact integer_range_ite (p 224) (d51202 p) (d51201 p) _ _ _ _ (bounds51202 p) (bounds51201 p)
theorem bounds51204 (p : Pattern) : (4 : Int) ≤ d51204 p ∧ d51204 p ≤ 12 := by
  exact integer_range_ite (p 204) (d51203 p) (d47616 p) _ _ _ _ (bounds51203 p) (bounds47616 p)
theorem bounds51231 (p : Pattern) : (10 : Int) ≤ d51231 p ∧ d51231 p ≤ 12 := by
  exact integer_range_ite (p 225) (d47928 p) (d47656 p) _ _ _ _ (bounds47928 p) (bounds47656 p)
theorem bounds51232 (p : Pattern) : (10 : Int) ≤ d51232 p ∧ d51232 p ≤ 12 := by
  exact integer_range_ite (p 224) (d47928 p) (d51231 p) _ _ _ _ (bounds47928 p) (bounds51231 p)
theorem bounds51233 (p : Pattern) : (10 : Int) ≤ d51233 p ∧ d51233 p ≤ 12 := by
  exact integer_range_ite (p 204) (d51232 p) (d47656 p) _ _ _ _ (bounds51232 p) (bounds47656 p)
theorem bounds51234 (p : Pattern) : (10 : Int) ≤ d51234 p ∧ d51234 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d51232 p) _ _ _ _ (bounds12 p) (bounds51232 p)
theorem bounds51235 (p : Pattern) : (10 : Int) ≤ d51235 p ∧ d51235 p ≤ 12 := by
  exact integer_range_ite (p 182) (d51234 p) (d51233 p) _ _ _ _ (bounds51234 p) (bounds51233 p)
theorem bounds51237 (p : Pattern) : (11 : Int) ≤ d51237 p ∧ d51237 p ≤ 12 := by
  exact integer_range_ite (p 204) (d51197 p) (d47638 p) _ _ _ _ (bounds51197 p) (bounds47638 p)
theorem bounds51238 (p : Pattern) : (11 : Int) ≤ d51238 p ∧ d51238 p ≤ 12 := by
  exact integer_range_ite (p 182) (d51198 p) (d51237 p) _ _ _ _ (bounds51198 p) (bounds51237 p)
theorem bounds51239 (p : Pattern) : (11 : Int) ≤ d51239 p ∧ d51239 p ≤ 12 := by
  exact integer_range_ite (p 163) (d12 p) (d51238 p) _ _ _ _ (bounds12 p) (bounds51238 p)
theorem bounds51268 (p : Pattern) : (4 : Int) ≤ d51268 p ∧ d51268 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d51203 p) _ _ _ _ (bounds12 p) (bounds51203 p)
theorem bounds51269 (p : Pattern) : (4 : Int) ≤ d51269 p ∧ d51269 p ≤ 12 := by
  exact integer_range_ite (p 182) (d51268 p) (d51204 p) _ _ _ _ (bounds51268 p) (bounds51204 p)
theorem bounds51278 (p : Pattern) : (6 : Int) ≤ d51278 p ∧ d51278 p ≤ 12 := by
  exact integer_range_ite (p 204) (d51192 p) (d47633 p) _ _ _ _ (bounds51192 p) (bounds47633 p)
theorem bounds51279 (p : Pattern) : (6 : Int) ≤ d51279 p ∧ d51279 p ≤ 12 := by
  exact integer_range_ite (p 182) (d51193 p) (d51278 p) _ _ _ _ (bounds51193 p) (bounds51278 p)
theorem bounds51287 (p : Pattern) : (4 : Int) ≤ d51287 p ∧ d51287 p ≤ 12 := by
  exact integer_range_ite (p 163) (d51235 p) (d51269 p) _ _ _ _ (bounds51235 p) (bounds51269 p)
theorem bounds51288 (p : Pattern) : (4 : Int) ≤ d51288 p ∧ d51288 p ≤ 12 := by
  exact integer_range_ite (p 162) (d51239 p) (d51287 p) _ _ _ _ (bounds51239 p) (bounds51287 p)
theorem bounds51290 (p : Pattern) : (6 : Int) ≤ d51290 p ∧ d51290 p ≤ 12 := by
  exact integer_range_ite (p 163) (d12 p) (d51279 p) _ _ _ _ (bounds12 p) (bounds51279 p)
theorem bounds51291 (p : Pattern) : (6 : Int) ≤ d51291 p ∧ d51291 p ≤ 12 := by
  exact integer_range_ite (p 162) (d12 p) (d51290 p) _ _ _ _ (bounds12 p) (bounds51290 p)
theorem bounds51347 (p : Pattern) : (5 : Int) ≤ d51347 p ∧ d51347 p ≤ 12 := by
  exact integer_range_ite (p 246) (d47622 p) (d47705 p) _ _ _ _ (bounds47622 p) (bounds47705 p)
theorem bounds51381 (p : Pattern) : (5 : Int) ≤ d51381 p ∧ d51381 p ≤ 12 := by
  exact integer_range_ite (p 246) (d47638 p) (d47705 p) _ _ _ _ (bounds47638 p) (bounds47705 p)
theorem bounds51382 (p : Pattern) : (5 : Int) ≤ d51382 p ∧ d51382 p ≤ 12 := by
  exact integer_range_ite (p 225) (d51381 p) (d47705 p) _ _ _ _ (bounds51381 p) (bounds47705 p)
theorem bounds51383 (p : Pattern) : (5 : Int) ≤ d51383 p ∧ d51383 p ≤ 12 := by
  exact integer_range_ite (p 225) (d47947 p) (d51347 p) _ _ _ _ (bounds47947 p) (bounds51347 p)
theorem bounds51384 (p : Pattern) : (5 : Int) ≤ d51384 p ∧ d51384 p ≤ 12 := by
  exact integer_range_ite (p 224) (d51383 p) (d51382 p) _ _ _ _ (bounds51383 p) (bounds51382 p)
theorem bounds51385 (p : Pattern) : (5 : Int) ≤ d51385 p ∧ d51385 p ≤ 12 := by
  exact integer_range_ite (p 204) (d51384 p) (d47705 p) _ _ _ _ (bounds51384 p) (bounds47705 p)
theorem bounds51430 (p : Pattern) : (5 : Int) ≤ d51430 p ∧ d51430 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d51384 p) _ _ _ _ (bounds12 p) (bounds51384 p)
theorem bounds51431 (p : Pattern) : (5 : Int) ≤ d51431 p ∧ d51431 p ≤ 12 := by
  exact integer_range_ite (p 182) (d51430 p) (d51385 p) _ _ _ _ (bounds51430 p) (bounds51385 p)
theorem bounds51446 (p : Pattern) : (5 : Int) ≤ d51446 p ∧ d51446 p ≤ 12 := by
  exact integer_range_ite (p 163) (d51238 p) (d51431 p) _ _ _ _ (bounds51238 p) (bounds51431 p)
theorem bounds51447 (p : Pattern) : (5 : Int) ≤ d51447 p ∧ d51447 p ≤ 12 := by
  exact integer_range_ite (p 162) (d12 p) (d51446 p) _ _ _ _ (bounds12 p) (bounds51446 p)
theorem bounds51530 (p : Pattern) : (4 : Int) ≤ d51530 p ∧ d51530 p ≤ 12 := by
  exact integer_range_ite (p 163) (d51238 p) (d51269 p) _ _ _ _ (bounds51238 p) (bounds51269 p)
theorem bounds338655 (p : Pattern) : (4 : Int) ≤ d338655 p ∧ d338655 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d4 p) _ _ _ _ (bounds12 p) (bounds4 p)
theorem bounds338656 (p : Pattern) : (4 : Int) ≤ d338656 p ∧ d338656 p ≤ 12 := by
  exact integer_range_ite (p 182) (d338655 p) (d4 p) _ _ _ _ (bounds338655 p) (bounds4 p)
theorem bounds338666 (p : Pattern) : (6 : Int) ≤ d338666 p ∧ d338666 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d6 p) _ _ _ _ (bounds12 p) (bounds6 p)
theorem bounds338669 (p : Pattern) : (11 : Int) ≤ d338669 p ∧ d338669 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d11 p) _ _ _ _ (bounds12 p) (bounds11 p)
theorem bounds338685 (p : Pattern) : (10 : Int) ≤ d338685 p ∧ d338685 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d10 p) _ _ _ _ (bounds12 p) (bounds10 p)
theorem bounds338686 (p : Pattern) : (10 : Int) ≤ d338686 p ∧ d338686 p ≤ 12 := by
  exact integer_range_ite (p 182) (d338685 p) (d10 p) _ _ _ _ (bounds338685 p) (bounds10 p)
theorem bounds338687 (p : Pattern) : (4 : Int) ≤ d338687 p ∧ d338687 p ≤ 12 := by
  exact integer_range_ite (p 163) (d338686 p) (d338656 p) _ _ _ _ (bounds338686 p) (bounds338656 p)
theorem bounds338688 (p : Pattern) : (11 : Int) ≤ d338688 p ∧ d338688 p ≤ 12 := by
  exact integer_range_ite (p 182) (d338669 p) (d11 p) _ _ _ _ (bounds338669 p) (bounds11 p)
theorem bounds338689 (p : Pattern) : (11 : Int) ≤ d338689 p ∧ d338689 p ≤ 12 := by
  exact integer_range_ite (p 163) (d12 p) (d338688 p) _ _ _ _ (bounds12 p) (bounds338688 p)
theorem bounds338690 (p : Pattern) : (4 : Int) ≤ d338690 p ∧ d338690 p ≤ 12 := by
  exact integer_range_ite (p 162) (d338689 p) (d338687 p) _ _ _ _ (bounds338689 p) (bounds338687 p)
theorem bounds338704 (p : Pattern) : (6 : Int) ≤ d338704 p ∧ d338704 p ≤ 12 := by
  exact integer_range_ite (p 182) (d338666 p) (d6 p) _ _ _ _ (bounds338666 p) (bounds6 p)
theorem bounds338709 (p : Pattern) : (6 : Int) ≤ d338709 p ∧ d338709 p ≤ 12 := by
  exact integer_range_ite (p 163) (d12 p) (d338704 p) _ _ _ _ (bounds12 p) (bounds338704 p)
theorem bounds338710 (p : Pattern) : (6 : Int) ≤ d338710 p ∧ d338710 p ≤ 12 := by
  exact integer_range_ite (p 162) (d12 p) (d338709 p) _ _ _ _ (bounds12 p) (bounds338709 p)
theorem bounds338730 (p : Pattern) : (5 : Int) ≤ d338730 p ∧ d338730 p ≤ 12 := by
  exact integer_range_ite (p 204) (d12 p) (d5 p) _ _ _ _ (bounds12 p) (bounds5 p)
theorem bounds338731 (p : Pattern) : (5 : Int) ≤ d338731 p ∧ d338731 p ≤ 12 := by
  exact integer_range_ite (p 182) (d338730 p) (d5 p) _ _ _ _ (bounds338730 p) (bounds5 p)
theorem bounds338754 (p : Pattern) : (5 : Int) ≤ d338754 p ∧ d338754 p ≤ 12 := by
  exact integer_range_ite (p 163) (d338688 p) (d338731 p) _ _ _ _ (bounds338688 p) (bounds338731 p)
theorem bounds338755 (p : Pattern) : (5 : Int) ≤ d338755 p ∧ d338755 p ≤ 12 := by
  exact integer_range_ite (p 162) (d12 p) (d338754 p) _ _ _ _ (bounds12 p) (bounds338754 p)
theorem bounds338814 (p : Pattern) : (4 : Int) ≤ d338814 p ∧ d338814 p ≤ 12 := by
  exact integer_range_ite (p 163) (d338688 p) (d338656 p) _ _ _ _ (bounds338688 p) (bounds338656 p)
end NetHack.Soko22Hazard87
