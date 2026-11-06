import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0263_0_checked : (List.range' 134656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0263_1_checked : (List.range' 134784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0263_2_checked : (List.range' 134912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0263_3_checked : (List.range' 135040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0263_range (index : Nat) (lower : 134656 ≤ index) (upper : index < 135168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 134912 then
    if cut : index < 134784 then
      exact segment_sound _ 134656 128 Restriction0263_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 134784 128 Restriction0263_1_checked index (by omega) (by omega)
  else
    if cut : index < 135040 then
      exact segment_sound _ 134912 128 Restriction0263_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 135040 128 Restriction0263_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
