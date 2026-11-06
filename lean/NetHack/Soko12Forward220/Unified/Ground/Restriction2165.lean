import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2165_0_checked : (List.range' 1108480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2165_1_checked : (List.range' 1108608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2165_2_checked : (List.range' 1108736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2165_3_checked : (List.range' 1108864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2165_range (index : Nat) (lower : 1108480 ≤ index) (upper : index < 1108992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1108736 then
    if cut : index < 1108608 then
      exact segment_sound _ 1108480 128 Restriction2165_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1108608 128 Restriction2165_1_checked index (by omega) (by omega)
  else
    if cut : index < 1108864 then
      exact segment_sound _ 1108736 128 Restriction2165_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1108864 128 Restriction2165_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
