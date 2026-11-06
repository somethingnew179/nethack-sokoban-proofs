import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0366_0_checked : (List.range' 187392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0366_1_checked : (List.range' 187520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0366_2_checked : (List.range' 187648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0366_3_checked : (List.range' 187776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0366_range (index : Nat) (lower : 187392 ≤ index) (upper : index < 187904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 187648 then
    if cut : index < 187520 then
      exact segment_sound _ 187392 128 Restriction0366_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 187520 128 Restriction0366_1_checked index (by omega) (by omega)
  else
    if cut : index < 187776 then
      exact segment_sound _ 187648 128 Restriction0366_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 187776 128 Restriction0366_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
