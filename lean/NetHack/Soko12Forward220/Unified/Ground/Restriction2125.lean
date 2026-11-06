import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2125_0_checked : (List.range' 1088000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2125_1_checked : (List.range' 1088128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2125_2_checked : (List.range' 1088256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2125_3_checked : (List.range' 1088384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2125_range (index : Nat) (lower : 1088000 ≤ index) (upper : index < 1088512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1088256 then
    if cut : index < 1088128 then
      exact segment_sound _ 1088000 128 Restriction2125_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1088128 128 Restriction2125_1_checked index (by omega) (by omega)
  else
    if cut : index < 1088384 then
      exact segment_sound _ 1088256 128 Restriction2125_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1088384 128 Restriction2125_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
