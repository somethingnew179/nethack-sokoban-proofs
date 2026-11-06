import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2373_0_checked : (List.range' 1214976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2373_1_checked : (List.range' 1215104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2373_2_checked : (List.range' 1215232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2373_3_checked : (List.range' 1215360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2373_range (index : Nat) (lower : 1214976 ≤ index) (upper : index < 1215488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1215232 then
    if cut : index < 1215104 then
      exact segment_sound _ 1214976 128 Restriction2373_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1215104 128 Restriction2373_1_checked index (by omega) (by omega)
  else
    if cut : index < 1215360 then
      exact segment_sound _ 1215232 128 Restriction2373_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1215360 128 Restriction2373_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
