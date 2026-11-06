import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1067_0_checked : (List.range' 546304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1067_1_checked : (List.range' 546432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1067_2_checked : (List.range' 546560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1067_3_checked : (List.range' 546688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1067_range (index : Nat) (lower : 546304 ≤ index) (upper : index < 546816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 546560 then
    if cut : index < 546432 then
      exact segment_sound _ 546304 128 Restriction1067_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 546432 128 Restriction1067_1_checked index (by omega) (by omega)
  else
    if cut : index < 546688 then
      exact segment_sound _ 546560 128 Restriction1067_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 546688 128 Restriction1067_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
