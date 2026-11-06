import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0259_0_checked : (List.range' 132608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0259_1_checked : (List.range' 132736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0259_2_checked : (List.range' 132864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0259_3_checked : (List.range' 132992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0259_range (index : Nat) (lower : 132608 ≤ index) (upper : index < 133120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 132864 then
    if cut : index < 132736 then
      exact segment_sound _ 132608 128 Restriction0259_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 132736 128 Restriction0259_1_checked index (by omega) (by omega)
  else
    if cut : index < 132992 then
      exact segment_sound _ 132864 128 Restriction0259_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 132992 128 Restriction0259_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
