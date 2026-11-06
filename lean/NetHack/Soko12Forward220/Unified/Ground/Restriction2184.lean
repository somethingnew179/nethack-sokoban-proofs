import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2184_0_checked : (List.range' 1118208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2184_1_checked : (List.range' 1118336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2184_2_checked : (List.range' 1118464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2184_3_checked : (List.range' 1118592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2184_range (index : Nat) (lower : 1118208 ≤ index) (upper : index < 1118720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1118464 then
    if cut : index < 1118336 then
      exact segment_sound _ 1118208 128 Restriction2184_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1118336 128 Restriction2184_1_checked index (by omega) (by omega)
  else
    if cut : index < 1118592 then
      exact segment_sound _ 1118464 128 Restriction2184_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1118592 128 Restriction2184_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
