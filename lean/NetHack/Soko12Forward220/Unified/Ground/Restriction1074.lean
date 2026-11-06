import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1074_0_checked : (List.range' 549888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1074_1_checked : (List.range' 550016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1074_2_checked : (List.range' 550144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1074_3_checked : (List.range' 550272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1074_range (index : Nat) (lower : 549888 ≤ index) (upper : index < 550400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 550144 then
    if cut : index < 550016 then
      exact segment_sound _ 549888 128 Restriction1074_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 550016 128 Restriction1074_1_checked index (by omega) (by omega)
  else
    if cut : index < 550272 then
      exact segment_sound _ 550144 128 Restriction1074_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 550272 128 Restriction1074_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
