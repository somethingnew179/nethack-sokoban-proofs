import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0109_0_checked : (List.range' 55808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0109_1_checked : (List.range' 55936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0109_2_checked : (List.range' 56064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0109_3_checked : (List.range' 56192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0109_range (index : Nat) (lower : 55808 ≤ index) (upper : index < 56320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 56064 then
    if cut : index < 55936 then
      exact segment_sound _ 55808 128 Restriction0109_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 55936 128 Restriction0109_1_checked index (by omega) (by omega)
  else
    if cut : index < 56192 then
      exact segment_sound _ 56064 128 Restriction0109_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 56192 128 Restriction0109_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
