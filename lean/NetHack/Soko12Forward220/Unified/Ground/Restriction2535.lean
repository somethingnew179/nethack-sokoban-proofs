import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2535_0_checked : (List.range' 1297920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2535_1_checked : (List.range' 1298048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2535_2_checked : (List.range' 1298176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2535_3_checked : (List.range' 1298304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2535_range (index : Nat) (lower : 1297920 ≤ index) (upper : index < 1298432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1298176 then
    if cut : index < 1298048 then
      exact segment_sound _ 1297920 128 Restriction2535_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1298048 128 Restriction2535_1_checked index (by omega) (by omega)
  else
    if cut : index < 1298304 then
      exact segment_sound _ 1298176 128 Restriction2535_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1298304 128 Restriction2535_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
