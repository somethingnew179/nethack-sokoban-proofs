import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2154_0_checked : (List.range' 1102848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2154_1_checked : (List.range' 1102976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2154_2_checked : (List.range' 1103104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2154_3_checked : (List.range' 1103232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2154_range (index : Nat) (lower : 1102848 ≤ index) (upper : index < 1103360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1103104 then
    if cut : index < 1102976 then
      exact segment_sound _ 1102848 128 Restriction2154_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1102976 128 Restriction2154_1_checked index (by omega) (by omega)
  else
    if cut : index < 1103232 then
      exact segment_sound _ 1103104 128 Restriction2154_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1103232 128 Restriction2154_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
