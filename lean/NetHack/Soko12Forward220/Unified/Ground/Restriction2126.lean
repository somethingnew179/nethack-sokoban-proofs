import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2126_0_checked : (List.range' 1088512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2126_1_checked : (List.range' 1088640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2126_2_checked : (List.range' 1088768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2126_3_checked : (List.range' 1088896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2126_range (index : Nat) (lower : 1088512 ≤ index) (upper : index < 1089024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1088768 then
    if cut : index < 1088640 then
      exact segment_sound _ 1088512 128 Restriction2126_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1088640 128 Restriction2126_1_checked index (by omega) (by omega)
  else
    if cut : index < 1088896 then
      exact segment_sound _ 1088768 128 Restriction2126_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1088896 128 Restriction2126_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
