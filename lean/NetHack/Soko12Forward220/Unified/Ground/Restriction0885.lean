import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0885_0_checked : (List.range' 453120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0885_1_checked : (List.range' 453248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0885_2_checked : (List.range' 453376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0885_3_checked : (List.range' 453504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0885_range (index : Nat) (lower : 453120 ≤ index) (upper : index < 453632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 453376 then
    if cut : index < 453248 then
      exact segment_sound _ 453120 128 Restriction0885_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 453248 128 Restriction0885_1_checked index (by omega) (by omega)
  else
    if cut : index < 453504 then
      exact segment_sound _ 453376 128 Restriction0885_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 453504 128 Restriction0885_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
