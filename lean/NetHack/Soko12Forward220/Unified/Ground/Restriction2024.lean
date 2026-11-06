import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2024_0_checked : (List.range' 1036288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2024_1_checked : (List.range' 1036416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2024_2_checked : (List.range' 1036544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2024_3_checked : (List.range' 1036672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2024_range (index : Nat) (lower : 1036288 ≤ index) (upper : index < 1036800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1036544 then
    if cut : index < 1036416 then
      exact segment_sound _ 1036288 128 Restriction2024_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1036416 128 Restriction2024_1_checked index (by omega) (by omega)
  else
    if cut : index < 1036672 then
      exact segment_sound _ 1036544 128 Restriction2024_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1036672 128 Restriction2024_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
