import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0834_0_checked : (List.range' 427008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0834_1_checked : (List.range' 427136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0834_2_checked : (List.range' 427264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0834_3_checked : (List.range' 427392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0834_range (index : Nat) (lower : 427008 ≤ index) (upper : index < 427520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 427264 then
    if cut : index < 427136 then
      exact segment_sound _ 427008 128 Restriction0834_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 427136 128 Restriction0834_1_checked index (by omega) (by omega)
  else
    if cut : index < 427392 then
      exact segment_sound _ 427264 128 Restriction0834_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 427392 128 Restriction0834_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
