import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1260_0_checked : (List.range' 645120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1260_1_checked : (List.range' 645248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1260_2_checked : (List.range' 645376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1260_3_checked : (List.range' 645504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1260_range (index : Nat) (lower : 645120 ≤ index) (upper : index < 645632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 645376 then
    if cut : index < 645248 then
      exact segment_sound _ 645120 128 Restriction1260_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 645248 128 Restriction1260_1_checked index (by omega) (by omega)
  else
    if cut : index < 645504 then
      exact segment_sound _ 645376 128 Restriction1260_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 645504 128 Restriction1260_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
