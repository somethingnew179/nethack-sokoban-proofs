import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1440_0_checked : (List.range' 737280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1440_1_checked : (List.range' 737408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1440_2_checked : (List.range' 737536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1440_3_checked : (List.range' 737664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1440_range (index : Nat) (lower : 737280 ≤ index) (upper : index < 737792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 737536 then
    if cut : index < 737408 then
      exact segment_sound _ 737280 128 Restriction1440_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 737408 128 Restriction1440_1_checked index (by omega) (by omega)
  else
    if cut : index < 737664 then
      exact segment_sound _ 737536 128 Restriction1440_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 737664 128 Restriction1440_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
