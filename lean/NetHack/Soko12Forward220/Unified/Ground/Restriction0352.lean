import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0352_0_checked : (List.range' 180224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0352_1_checked : (List.range' 180352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0352_2_checked : (List.range' 180480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0352_3_checked : (List.range' 180608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0352_range (index : Nat) (lower : 180224 ≤ index) (upper : index < 180736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 180480 then
    if cut : index < 180352 then
      exact segment_sound _ 180224 128 Restriction0352_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 180352 128 Restriction0352_1_checked index (by omega) (by omega)
  else
    if cut : index < 180608 then
      exact segment_sound _ 180480 128 Restriction0352_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 180608 128 Restriction0352_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
