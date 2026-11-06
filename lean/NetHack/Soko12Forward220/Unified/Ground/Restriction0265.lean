import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0265_0_checked : (List.range' 135680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0265_1_checked : (List.range' 135808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0265_2_checked : (List.range' 135936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0265_3_checked : (List.range' 136064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0265_range (index : Nat) (lower : 135680 ≤ index) (upper : index < 136192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 135936 then
    if cut : index < 135808 then
      exact segment_sound _ 135680 128 Restriction0265_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 135808 128 Restriction0265_1_checked index (by omega) (by omega)
  else
    if cut : index < 136064 then
      exact segment_sound _ 135936 128 Restriction0265_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 136064 128 Restriction0265_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
