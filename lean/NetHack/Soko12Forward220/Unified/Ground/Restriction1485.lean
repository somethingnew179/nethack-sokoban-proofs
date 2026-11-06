import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1485_0_checked : (List.range' 760320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1485_1_checked : (List.range' 760448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1485_2_checked : (List.range' 760576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1485_3_checked : (List.range' 760704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1485_range (index : Nat) (lower : 760320 ≤ index) (upper : index < 760832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 760576 then
    if cut : index < 760448 then
      exact segment_sound _ 760320 128 Restriction1485_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 760448 128 Restriction1485_1_checked index (by omega) (by omega)
  else
    if cut : index < 760704 then
      exact segment_sound _ 760576 128 Restriction1485_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 760704 128 Restriction1485_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
