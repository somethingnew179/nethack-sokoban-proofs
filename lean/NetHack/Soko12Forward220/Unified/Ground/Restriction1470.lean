import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1470_0_checked : (List.range' 752640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1470_1_checked : (List.range' 752768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1470_2_checked : (List.range' 752896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1470_3_checked : (List.range' 753024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1470_range (index : Nat) (lower : 752640 ≤ index) (upper : index < 753152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 752896 then
    if cut : index < 752768 then
      exact segment_sound _ 752640 128 Restriction1470_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 752768 128 Restriction1470_1_checked index (by omega) (by omega)
  else
    if cut : index < 753024 then
      exact segment_sound _ 752896 128 Restriction1470_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 753024 128 Restriction1470_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
