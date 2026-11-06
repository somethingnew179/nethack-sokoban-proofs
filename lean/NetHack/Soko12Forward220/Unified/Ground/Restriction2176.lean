import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2176_0_checked : (List.range' 1114112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2176_1_checked : (List.range' 1114240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2176_2_checked : (List.range' 1114368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2176_3_checked : (List.range' 1114496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2176_range (index : Nat) (lower : 1114112 ≤ index) (upper : index < 1114624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1114368 then
    if cut : index < 1114240 then
      exact segment_sound _ 1114112 128 Restriction2176_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1114240 128 Restriction2176_1_checked index (by omega) (by omega)
  else
    if cut : index < 1114496 then
      exact segment_sound _ 1114368 128 Restriction2176_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1114496 128 Restriction2176_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
