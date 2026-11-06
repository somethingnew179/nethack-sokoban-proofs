import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2456_0_checked : (List.range' 1257472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2456_1_checked : (List.range' 1257600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2456_2_checked : (List.range' 1257728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2456_3_checked : (List.range' 1257856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2456_range (index : Nat) (lower : 1257472 ≤ index) (upper : index < 1257984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1257728 then
    if cut : index < 1257600 then
      exact segment_sound _ 1257472 128 Restriction2456_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1257600 128 Restriction2456_1_checked index (by omega) (by omega)
  else
    if cut : index < 1257856 then
      exact segment_sound _ 1257728 128 Restriction2456_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1257856 128 Restriction2456_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
