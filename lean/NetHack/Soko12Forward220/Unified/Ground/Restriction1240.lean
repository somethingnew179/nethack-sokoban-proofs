import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1240_0_checked : (List.range' 634880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1240_1_checked : (List.range' 635008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1240_2_checked : (List.range' 635136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1240_3_checked : (List.range' 635264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1240_range (index : Nat) (lower : 634880 ≤ index) (upper : index < 635392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 635136 then
    if cut : index < 635008 then
      exact segment_sound _ 634880 128 Restriction1240_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 635008 128 Restriction1240_1_checked index (by omega) (by omega)
  else
    if cut : index < 635264 then
      exact segment_sound _ 635136 128 Restriction1240_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 635264 128 Restriction1240_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
