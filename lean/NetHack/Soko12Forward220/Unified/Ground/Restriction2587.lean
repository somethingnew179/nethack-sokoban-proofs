import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2587_0_checked : (List.range' 1324544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2587_1_checked : (List.range' 1324672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2587_2_checked : (List.range' 1324800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2587_3_checked : (List.range' 1324928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2587_range (index : Nat) (lower : 1324544 ≤ index) (upper : index < 1325056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1324800 then
    if cut : index < 1324672 then
      exact segment_sound _ 1324544 128 Restriction2587_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1324672 128 Restriction2587_1_checked index (by omega) (by omega)
  else
    if cut : index < 1324928 then
      exact segment_sound _ 1324800 128 Restriction2587_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1324928 128 Restriction2587_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
