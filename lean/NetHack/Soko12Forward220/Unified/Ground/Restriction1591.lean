import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1591_0_checked : (List.range' 814592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1591_1_checked : (List.range' 814720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1591_2_checked : (List.range' 814848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1591_3_checked : (List.range' 814976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1591_range (index : Nat) (lower : 814592 ≤ index) (upper : index < 815104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 814848 then
    if cut : index < 814720 then
      exact segment_sound _ 814592 128 Restriction1591_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 814720 128 Restriction1591_1_checked index (by omega) (by omega)
  else
    if cut : index < 814976 then
      exact segment_sound _ 814848 128 Restriction1591_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 814976 128 Restriction1591_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
