import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0291_0_checked : (List.range' 148992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0291_1_checked : (List.range' 149120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0291_2_checked : (List.range' 149248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0291_3_checked : (List.range' 149376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0291_range (index : Nat) (lower : 148992 ≤ index) (upper : index < 149504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 149248 then
    if cut : index < 149120 then
      exact segment_sound _ 148992 128 Restriction0291_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 149120 128 Restriction0291_1_checked index (by omega) (by omega)
  else
    if cut : index < 149376 then
      exact segment_sound _ 149248 128 Restriction0291_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 149376 128 Restriction0291_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
