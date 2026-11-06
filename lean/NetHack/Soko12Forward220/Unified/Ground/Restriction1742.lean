import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1742_0_checked : (List.range' 891904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1742_1_checked : (List.range' 892032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1742_2_checked : (List.range' 892160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1742_3_checked : (List.range' 892288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1742_range (index : Nat) (lower : 891904 ≤ index) (upper : index < 892416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 892160 then
    if cut : index < 892032 then
      exact segment_sound _ 891904 128 Restriction1742_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 892032 128 Restriction1742_1_checked index (by omega) (by omega)
  else
    if cut : index < 892288 then
      exact segment_sound _ 892160 128 Restriction1742_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 892288 128 Restriction1742_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
