import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0015_0_checked : (List.range' 7680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0015_1_checked : (List.range' 7808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0015_2_checked : (List.range' 7936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0015_3_checked : (List.range' 8064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0015_range (index : Nat) (lower : 7680 ≤ index) (upper : index < 8192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 7936 then
    if cut : index < 7808 then
      exact segment_sound _ 7680 128 Restriction0015_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 7808 128 Restriction0015_1_checked index (by omega) (by omega)
  else
    if cut : index < 8064 then
      exact segment_sound _ 7936 128 Restriction0015_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 8064 128 Restriction0015_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
