import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1714_0_checked : (List.range' 877568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1714_1_checked : (List.range' 877696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1714_2_checked : (List.range' 877824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1714_3_checked : (List.range' 877952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1714_range (index : Nat) (lower : 877568 ≤ index) (upper : index < 878080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 877824 then
    if cut : index < 877696 then
      exact segment_sound _ 877568 128 Restriction1714_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 877696 128 Restriction1714_1_checked index (by omega) (by omega)
  else
    if cut : index < 877952 then
      exact segment_sound _ 877824 128 Restriction1714_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 877952 128 Restriction1714_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
