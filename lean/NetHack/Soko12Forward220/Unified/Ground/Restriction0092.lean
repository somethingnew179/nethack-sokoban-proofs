import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0092_0_checked : (List.range' 47104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0092_1_checked : (List.range' 47232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0092_2_checked : (List.range' 47360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0092_3_checked : (List.range' 47488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0092_range (index : Nat) (lower : 47104 ≤ index) (upper : index < 47616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 47360 then
    if cut : index < 47232 then
      exact segment_sound _ 47104 128 Restriction0092_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 47232 128 Restriction0092_1_checked index (by omega) (by omega)
  else
    if cut : index < 47488 then
      exact segment_sound _ 47360 128 Restriction0092_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 47488 128 Restriction0092_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
