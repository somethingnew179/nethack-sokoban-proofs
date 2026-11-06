import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0447_0_checked : (List.range' 228864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0447_1_checked : (List.range' 228992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0447_2_checked : (List.range' 229120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0447_3_checked : (List.range' 229248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0447_range (index : Nat) (lower : 228864 ≤ index) (upper : index < 229376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 229120 then
    if cut : index < 228992 then
      exact segment_sound _ 228864 128 Restriction0447_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 228992 128 Restriction0447_1_checked index (by omega) (by omega)
  else
    if cut : index < 229248 then
      exact segment_sound _ 229120 128 Restriction0447_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 229248 128 Restriction0447_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
