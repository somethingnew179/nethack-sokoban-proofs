import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1093_0_checked : (List.range' 559616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1093_1_checked : (List.range' 559744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1093_2_checked : (List.range' 559872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1093_3_checked : (List.range' 560000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1093_range (index : Nat) (lower : 559616 ≤ index) (upper : index < 560128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 559872 then
    if cut : index < 559744 then
      exact segment_sound _ 559616 128 Restriction1093_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 559744 128 Restriction1093_1_checked index (by omega) (by omega)
  else
    if cut : index < 560000 then
      exact segment_sound _ 559872 128 Restriction1093_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 560000 128 Restriction1093_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
