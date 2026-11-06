import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0529_0_checked : (List.range' 270848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0529_1_checked : (List.range' 270976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0529_2_checked : (List.range' 271104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0529_3_checked : (List.range' 271232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0529_range (index : Nat) (lower : 270848 ≤ index) (upper : index < 271360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 271104 then
    if cut : index < 270976 then
      exact segment_sound _ 270848 128 Restriction0529_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 270976 128 Restriction0529_1_checked index (by omega) (by omega)
  else
    if cut : index < 271232 then
      exact segment_sound _ 271104 128 Restriction0529_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 271232 128 Restriction0529_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
