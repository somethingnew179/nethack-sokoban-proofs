import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0779_0_checked : (List.range' 398848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0779_1_checked : (List.range' 398976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0779_2_checked : (List.range' 399104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0779_3_checked : (List.range' 399232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0779_range (index : Nat) (lower : 398848 ≤ index) (upper : index < 399360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 399104 then
    if cut : index < 398976 then
      exact segment_sound _ 398848 128 Restriction0779_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 398976 128 Restriction0779_1_checked index (by omega) (by omega)
  else
    if cut : index < 399232 then
      exact segment_sound _ 399104 128 Restriction0779_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 399232 128 Restriction0779_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
