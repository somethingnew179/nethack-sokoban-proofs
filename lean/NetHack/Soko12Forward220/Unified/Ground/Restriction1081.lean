import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1081_0_checked : (List.range' 553472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1081_1_checked : (List.range' 553600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1081_2_checked : (List.range' 553728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1081_3_checked : (List.range' 553856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1081_range (index : Nat) (lower : 553472 ≤ index) (upper : index < 553984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 553728 then
    if cut : index < 553600 then
      exact segment_sound _ 553472 128 Restriction1081_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 553600 128 Restriction1081_1_checked index (by omega) (by omega)
  else
    if cut : index < 553856 then
      exact segment_sound _ 553728 128 Restriction1081_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 553856 128 Restriction1081_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
