import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1919_0_checked : (List.range' 982528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1919_1_checked : (List.range' 982656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1919_2_checked : (List.range' 982784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1919_3_checked : (List.range' 982912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1919_range (index : Nat) (lower : 982528 ≤ index) (upper : index < 983040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 982784 then
    if cut : index < 982656 then
      exact segment_sound _ 982528 128 Restriction1919_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 982656 128 Restriction1919_1_checked index (by omega) (by omega)
  else
    if cut : index < 982912 then
      exact segment_sound _ 982784 128 Restriction1919_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 982912 128 Restriction1919_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
