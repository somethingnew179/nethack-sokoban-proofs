import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1449_0_checked : (List.range' 741888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1449_1_checked : (List.range' 742016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1449_2_checked : (List.range' 742144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1449_3_checked : (List.range' 742272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1449_range (index : Nat) (lower : 741888 ≤ index) (upper : index < 742400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 742144 then
    if cut : index < 742016 then
      exact segment_sound _ 741888 128 Restriction1449_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 742016 128 Restriction1449_1_checked index (by omega) (by omega)
  else
    if cut : index < 742272 then
      exact segment_sound _ 742144 128 Restriction1449_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 742272 128 Restriction1449_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
