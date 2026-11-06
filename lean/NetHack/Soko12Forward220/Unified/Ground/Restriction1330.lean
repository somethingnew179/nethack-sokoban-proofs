import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1330_0_checked : (List.range' 680960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1330_1_checked : (List.range' 681088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1330_2_checked : (List.range' 681216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1330_3_checked : (List.range' 681344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1330_range (index : Nat) (lower : 680960 ≤ index) (upper : index < 681472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 681216 then
    if cut : index < 681088 then
      exact segment_sound _ 680960 128 Restriction1330_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 681088 128 Restriction1330_1_checked index (by omega) (by omega)
  else
    if cut : index < 681344 then
      exact segment_sound _ 681216 128 Restriction1330_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 681344 128 Restriction1330_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
