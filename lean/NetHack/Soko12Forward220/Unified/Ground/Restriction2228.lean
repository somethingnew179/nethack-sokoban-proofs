import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2228_0_checked : (List.range' 1140736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2228_1_checked : (List.range' 1140864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2228_2_checked : (List.range' 1140992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2228_3_checked : (List.range' 1141120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2228_range (index : Nat) (lower : 1140736 ≤ index) (upper : index < 1141248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1140992 then
    if cut : index < 1140864 then
      exact segment_sound _ 1140736 128 Restriction2228_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1140864 128 Restriction2228_1_checked index (by omega) (by omega)
  else
    if cut : index < 1141120 then
      exact segment_sound _ 1140992 128 Restriction2228_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1141120 128 Restriction2228_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
