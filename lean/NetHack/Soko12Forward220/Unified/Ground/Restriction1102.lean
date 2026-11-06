import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1102_0_checked : (List.range' 564224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1102_1_checked : (List.range' 564352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1102_2_checked : (List.range' 564480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1102_3_checked : (List.range' 564608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1102_range (index : Nat) (lower : 564224 ≤ index) (upper : index < 564736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 564480 then
    if cut : index < 564352 then
      exact segment_sound _ 564224 128 Restriction1102_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 564352 128 Restriction1102_1_checked index (by omega) (by omega)
  else
    if cut : index < 564608 then
      exact segment_sound _ 564480 128 Restriction1102_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 564608 128 Restriction1102_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
