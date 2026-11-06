import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2459_0_checked : (List.range' 1259008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2459_1_checked : (List.range' 1259136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2459_2_checked : (List.range' 1259264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2459_3_checked : (List.range' 1259392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2459_range (index : Nat) (lower : 1259008 ≤ index) (upper : index < 1259520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1259264 then
    if cut : index < 1259136 then
      exact segment_sound _ 1259008 128 Restriction2459_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1259136 128 Restriction2459_1_checked index (by omega) (by omega)
  else
    if cut : index < 1259392 then
      exact segment_sound _ 1259264 128 Restriction2459_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1259392 128 Restriction2459_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
