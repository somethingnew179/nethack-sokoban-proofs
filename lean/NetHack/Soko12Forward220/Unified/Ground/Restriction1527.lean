import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1527_0_checked : (List.range' 781824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1527_1_checked : (List.range' 781952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1527_2_checked : (List.range' 782080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1527_3_checked : (List.range' 782208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1527_range (index : Nat) (lower : 781824 ≤ index) (upper : index < 782336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 782080 then
    if cut : index < 781952 then
      exact segment_sound _ 781824 128 Restriction1527_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 781952 128 Restriction1527_1_checked index (by omega) (by omega)
  else
    if cut : index < 782208 then
      exact segment_sound _ 782080 128 Restriction1527_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 782208 128 Restriction1527_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
