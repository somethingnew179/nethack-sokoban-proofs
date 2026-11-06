import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2581_0_checked : (List.range' 1321472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2581_1_checked : (List.range' 1321600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2581_2_checked : (List.range' 1321728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2581_3_checked : (List.range' 1321856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2581_range (index : Nat) (lower : 1321472 ≤ index) (upper : index < 1321984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1321728 then
    if cut : index < 1321600 then
      exact segment_sound _ 1321472 128 Restriction2581_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1321600 128 Restriction2581_1_checked index (by omega) (by omega)
  else
    if cut : index < 1321856 then
      exact segment_sound _ 1321728 128 Restriction2581_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1321856 128 Restriction2581_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
