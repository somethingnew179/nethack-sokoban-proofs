import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2023_0_checked : (List.range' 1035776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2023_1_checked : (List.range' 1035904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2023_2_checked : (List.range' 1036032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2023_3_checked : (List.range' 1036160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2023_range (index : Nat) (lower : 1035776 ≤ index) (upper : index < 1036288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1036032 then
    if cut : index < 1035904 then
      exact segment_sound _ 1035776 128 Restriction2023_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1035904 128 Restriction2023_1_checked index (by omega) (by omega)
  else
    if cut : index < 1036160 then
      exact segment_sound _ 1036032 128 Restriction2023_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1036160 128 Restriction2023_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
