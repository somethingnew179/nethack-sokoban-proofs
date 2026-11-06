import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1197_0_checked : (List.range' 612864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1197_1_checked : (List.range' 612992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1197_2_checked : (List.range' 613120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1197_3_checked : (List.range' 613248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1197_range (index : Nat) (lower : 612864 ≤ index) (upper : index < 613376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 613120 then
    if cut : index < 612992 then
      exact segment_sound _ 612864 128 Restriction1197_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 612992 128 Restriction1197_1_checked index (by omega) (by omega)
  else
    if cut : index < 613248 then
      exact segment_sound _ 613120 128 Restriction1197_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 613248 128 Restriction1197_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
