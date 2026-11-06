import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1161_0_checked : (List.range' 594432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1161_1_checked : (List.range' 594560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1161_2_checked : (List.range' 594688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1161_3_checked : (List.range' 594816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1161_range (index : Nat) (lower : 594432 ≤ index) (upper : index < 594944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 594688 then
    if cut : index < 594560 then
      exact segment_sound _ 594432 128 Restriction1161_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 594560 128 Restriction1161_1_checked index (by omega) (by omega)
  else
    if cut : index < 594816 then
      exact segment_sound _ 594688 128 Restriction1161_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 594816 128 Restriction1161_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
