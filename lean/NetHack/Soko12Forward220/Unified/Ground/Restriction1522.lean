import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1522_0_checked : (List.range' 779264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1522_1_checked : (List.range' 779392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1522_2_checked : (List.range' 779520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1522_3_checked : (List.range' 779648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1522_range (index : Nat) (lower : 779264 ≤ index) (upper : index < 779776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 779520 then
    if cut : index < 779392 then
      exact segment_sound _ 779264 128 Restriction1522_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 779392 128 Restriction1522_1_checked index (by omega) (by omega)
  else
    if cut : index < 779648 then
      exact segment_sound _ 779520 128 Restriction1522_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 779648 128 Restriction1522_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
