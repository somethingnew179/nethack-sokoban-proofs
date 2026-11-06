import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0703_0_checked : (List.range' 359936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0703_1_checked : (List.range' 360064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0703_2_checked : (List.range' 360192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0703_3_checked : (List.range' 360320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0703_range (index : Nat) (lower : 359936 ≤ index) (upper : index < 360448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 360192 then
    if cut : index < 360064 then
      exact segment_sound _ 359936 128 Restriction0703_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 360064 128 Restriction0703_1_checked index (by omega) (by omega)
  else
    if cut : index < 360320 then
      exact segment_sound _ 360192 128 Restriction0703_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 360320 128 Restriction0703_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
