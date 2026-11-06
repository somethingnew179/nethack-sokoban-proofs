import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1426_0_checked : (List.range' 730112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1426_1_checked : (List.range' 730240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1426_2_checked : (List.range' 730368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1426_3_checked : (List.range' 730496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1426_range (index : Nat) (lower : 730112 ≤ index) (upper : index < 730624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 730368 then
    if cut : index < 730240 then
      exact segment_sound _ 730112 128 Restriction1426_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 730240 128 Restriction1426_1_checked index (by omega) (by omega)
  else
    if cut : index < 730496 then
      exact segment_sound _ 730368 128 Restriction1426_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 730496 128 Restriction1426_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
