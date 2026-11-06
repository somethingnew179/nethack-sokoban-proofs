import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0888_0_checked : (List.range' 454656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0888_1_checked : (List.range' 454784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0888_2_checked : (List.range' 454912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0888_3_checked : (List.range' 455040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0888_range (index : Nat) (lower : 454656 ≤ index) (upper : index < 455168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 454912 then
    if cut : index < 454784 then
      exact segment_sound _ 454656 128 Restriction0888_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 454784 128 Restriction0888_1_checked index (by omega) (by omega)
  else
    if cut : index < 455040 then
      exact segment_sound _ 454912 128 Restriction0888_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 455040 128 Restriction0888_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
