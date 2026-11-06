import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2565_0_checked : (List.range' 1313280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2565_1_checked : (List.range' 1313408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2565_2_checked : (List.range' 1313536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2565_3_checked : (List.range' 1313664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2565_range (index : Nat) (lower : 1313280 ≤ index) (upper : index < 1313792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1313536 then
    if cut : index < 1313408 then
      exact segment_sound _ 1313280 128 Restriction2565_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1313408 128 Restriction2565_1_checked index (by omega) (by omega)
  else
    if cut : index < 1313664 then
      exact segment_sound _ 1313536 128 Restriction2565_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1313664 128 Restriction2565_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
