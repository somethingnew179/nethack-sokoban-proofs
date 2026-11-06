import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1401_0_checked : (List.range' 717312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1401_1_checked : (List.range' 717440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1401_2_checked : (List.range' 717568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1401_3_checked : (List.range' 717696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1401_range (index : Nat) (lower : 717312 ≤ index) (upper : index < 717824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 717568 then
    if cut : index < 717440 then
      exact segment_sound _ 717312 128 Restriction1401_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 717440 128 Restriction1401_1_checked index (by omega) (by omega)
  else
    if cut : index < 717696 then
      exact segment_sound _ 717568 128 Restriction1401_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 717696 128 Restriction1401_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
