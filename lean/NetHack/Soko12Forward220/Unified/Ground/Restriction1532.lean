import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1532_0_checked : (List.range' 784384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1532_1_checked : (List.range' 784512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1532_2_checked : (List.range' 784640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1532_3_checked : (List.range' 784768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1532_range (index : Nat) (lower : 784384 ≤ index) (upper : index < 784896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 784640 then
    if cut : index < 784512 then
      exact segment_sound _ 784384 128 Restriction1532_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 784512 128 Restriction1532_1_checked index (by omega) (by omega)
  else
    if cut : index < 784768 then
      exact segment_sound _ 784640 128 Restriction1532_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 784768 128 Restriction1532_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
