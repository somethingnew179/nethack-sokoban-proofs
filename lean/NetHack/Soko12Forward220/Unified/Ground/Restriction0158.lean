import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0158_0_checked : (List.range' 80896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0158_1_checked : (List.range' 81024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0158_2_checked : (List.range' 81152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0158_3_checked : (List.range' 81280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0158_range (index : Nat) (lower : 80896 ≤ index) (upper : index < 81408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 81152 then
    if cut : index < 81024 then
      exact segment_sound _ 80896 128 Restriction0158_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 81024 128 Restriction0158_1_checked index (by omega) (by omega)
  else
    if cut : index < 81280 then
      exact segment_sound _ 81152 128 Restriction0158_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 81280 128 Restriction0158_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
