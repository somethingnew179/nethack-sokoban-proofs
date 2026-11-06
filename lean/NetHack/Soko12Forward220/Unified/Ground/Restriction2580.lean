import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2580_0_checked : (List.range' 1320960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2580_1_checked : (List.range' 1321088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2580_2_checked : (List.range' 1321216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2580_3_checked : (List.range' 1321344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2580_range (index : Nat) (lower : 1320960 ≤ index) (upper : index < 1321472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1321216 then
    if cut : index < 1321088 then
      exact segment_sound _ 1320960 128 Restriction2580_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1321088 128 Restriction2580_1_checked index (by omega) (by omega)
  else
    if cut : index < 1321344 then
      exact segment_sound _ 1321216 128 Restriction2580_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1321344 128 Restriction2580_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
