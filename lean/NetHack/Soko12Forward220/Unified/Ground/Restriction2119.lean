import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2119_0_checked : (List.range' 1084928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2119_1_checked : (List.range' 1085056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2119_2_checked : (List.range' 1085184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2119_3_checked : (List.range' 1085312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2119_range (index : Nat) (lower : 1084928 ≤ index) (upper : index < 1085440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1085184 then
    if cut : index < 1085056 then
      exact segment_sound _ 1084928 128 Restriction2119_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1085056 128 Restriction2119_1_checked index (by omega) (by omega)
  else
    if cut : index < 1085312 then
      exact segment_sound _ 1085184 128 Restriction2119_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1085312 128 Restriction2119_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
