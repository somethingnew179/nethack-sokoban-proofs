import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1010_0_checked : (List.range' 517120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1010_1_checked : (List.range' 517248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1010_2_checked : (List.range' 517376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1010_3_checked : (List.range' 517504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1010_range (index : Nat) (lower : 517120 ≤ index) (upper : index < 517632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 517376 then
    if cut : index < 517248 then
      exact segment_sound _ 517120 128 Restriction1010_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 517248 128 Restriction1010_1_checked index (by omega) (by omega)
  else
    if cut : index < 517504 then
      exact segment_sound _ 517376 128 Restriction1010_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 517504 128 Restriction1010_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
