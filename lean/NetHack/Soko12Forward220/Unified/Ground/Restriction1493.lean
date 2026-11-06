import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1493_0_checked : (List.range' 764416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1493_1_checked : (List.range' 764544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1493_2_checked : (List.range' 764672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1493_3_checked : (List.range' 764800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1493_range (index : Nat) (lower : 764416 ≤ index) (upper : index < 764928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 764672 then
    if cut : index < 764544 then
      exact segment_sound _ 764416 128 Restriction1493_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 764544 128 Restriction1493_1_checked index (by omega) (by omega)
  else
    if cut : index < 764800 then
      exact segment_sound _ 764672 128 Restriction1493_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 764800 128 Restriction1493_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
