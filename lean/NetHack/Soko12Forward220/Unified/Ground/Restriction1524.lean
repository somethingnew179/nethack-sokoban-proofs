import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1524_0_checked : (List.range' 780288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1524_1_checked : (List.range' 780416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1524_2_checked : (List.range' 780544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1524_3_checked : (List.range' 780672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1524_range (index : Nat) (lower : 780288 ≤ index) (upper : index < 780800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 780544 then
    if cut : index < 780416 then
      exact segment_sound _ 780288 128 Restriction1524_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 780416 128 Restriction1524_1_checked index (by omega) (by omega)
  else
    if cut : index < 780672 then
      exact segment_sound _ 780544 128 Restriction1524_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 780672 128 Restriction1524_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
