import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1717_0_checked : (List.range' 879104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1717_1_checked : (List.range' 879232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1717_2_checked : (List.range' 879360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1717_3_checked : (List.range' 879488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1717_range (index : Nat) (lower : 879104 ≤ index) (upper : index < 879616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 879360 then
    if cut : index < 879232 then
      exact segment_sound _ 879104 128 Restriction1717_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 879232 128 Restriction1717_1_checked index (by omega) (by omega)
  else
    if cut : index < 879488 then
      exact segment_sound _ 879360 128 Restriction1717_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 879488 128 Restriction1717_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
