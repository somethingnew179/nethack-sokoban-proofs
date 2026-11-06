import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1214_0_checked : (List.range' 621568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1214_1_checked : (List.range' 621696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1214_2_checked : (List.range' 621824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1214_3_checked : (List.range' 621952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1214_range (index : Nat) (lower : 621568 ≤ index) (upper : index < 622080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 621824 then
    if cut : index < 621696 then
      exact segment_sound _ 621568 128 Restriction1214_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 621696 128 Restriction1214_1_checked index (by omega) (by omega)
  else
    if cut : index < 621952 then
      exact segment_sound _ 621824 128 Restriction1214_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 621952 128 Restriction1214_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
