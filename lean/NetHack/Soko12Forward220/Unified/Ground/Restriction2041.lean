import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2041_0_checked : (List.range' 1044992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2041_1_checked : (List.range' 1045120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2041_2_checked : (List.range' 1045248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2041_3_checked : (List.range' 1045376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2041_range (index : Nat) (lower : 1044992 ≤ index) (upper : index < 1045504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1045248 then
    if cut : index < 1045120 then
      exact segment_sound _ 1044992 128 Restriction2041_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1045120 128 Restriction2041_1_checked index (by omega) (by omega)
  else
    if cut : index < 1045376 then
      exact segment_sound _ 1045248 128 Restriction2041_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1045376 128 Restriction2041_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
