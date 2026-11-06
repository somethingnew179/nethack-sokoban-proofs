import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0697_0_checked : (List.range' 356864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0697_1_checked : (List.range' 356992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0697_2_checked : (List.range' 357120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0697_3_checked : (List.range' 357248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0697_range (index : Nat) (lower : 356864 ≤ index) (upper : index < 357376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 357120 then
    if cut : index < 356992 then
      exact segment_sound _ 356864 128 Restriction0697_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 356992 128 Restriction0697_1_checked index (by omega) (by omega)
  else
    if cut : index < 357248 then
      exact segment_sound _ 357120 128 Restriction0697_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 357248 128 Restriction0697_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
