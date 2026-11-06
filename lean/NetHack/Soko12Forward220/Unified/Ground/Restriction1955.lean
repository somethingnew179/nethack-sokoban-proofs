import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1955_0_checked : (List.range' 1000960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1955_1_checked : (List.range' 1001088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1955_2_checked : (List.range' 1001216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1955_3_checked : (List.range' 1001344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1955_range (index : Nat) (lower : 1000960 ≤ index) (upper : index < 1001472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1001216 then
    if cut : index < 1001088 then
      exact segment_sound _ 1000960 128 Restriction1955_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1001088 128 Restriction1955_1_checked index (by omega) (by omega)
  else
    if cut : index < 1001344 then
      exact segment_sound _ 1001216 128 Restriction1955_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1001344 128 Restriction1955_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
