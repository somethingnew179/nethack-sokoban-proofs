import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1921_0_checked : (List.range' 983552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1921_1_checked : (List.range' 983680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1921_2_checked : (List.range' 983808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1921_3_checked : (List.range' 983936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1921_range (index : Nat) (lower : 983552 ≤ index) (upper : index < 984064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 983808 then
    if cut : index < 983680 then
      exact segment_sound _ 983552 128 Restriction1921_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 983680 128 Restriction1921_1_checked index (by omega) (by omega)
  else
    if cut : index < 983936 then
      exact segment_sound _ 983808 128 Restriction1921_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 983936 128 Restriction1921_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
