import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1119_0_checked : (List.range' 572928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1119_1_checked : (List.range' 573056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1119_2_checked : (List.range' 573184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1119_3_checked : (List.range' 573312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1119_range (index : Nat) (lower : 572928 ≤ index) (upper : index < 573440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 573184 then
    if cut : index < 573056 then
      exact segment_sound _ 572928 128 Restriction1119_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 573056 128 Restriction1119_1_checked index (by omega) (by omega)
  else
    if cut : index < 573312 then
      exact segment_sound _ 573184 128 Restriction1119_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 573312 128 Restriction1119_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
