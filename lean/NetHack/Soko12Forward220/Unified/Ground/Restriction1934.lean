import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1934_0_checked : (List.range' 990208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1934_1_checked : (List.range' 990336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1934_2_checked : (List.range' 990464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1934_3_checked : (List.range' 990592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1934_range (index : Nat) (lower : 990208 ≤ index) (upper : index < 990720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 990464 then
    if cut : index < 990336 then
      exact segment_sound _ 990208 128 Restriction1934_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 990336 128 Restriction1934_1_checked index (by omega) (by omega)
  else
    if cut : index < 990592 then
      exact segment_sound _ 990464 128 Restriction1934_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 990592 128 Restriction1934_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
