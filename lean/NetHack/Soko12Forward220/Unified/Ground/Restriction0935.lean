import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0935_0_checked : (List.range' 478720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0935_1_checked : (List.range' 478848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0935_2_checked : (List.range' 478976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0935_3_checked : (List.range' 479104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0935_range (index : Nat) (lower : 478720 ≤ index) (upper : index < 479232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 478976 then
    if cut : index < 478848 then
      exact segment_sound _ 478720 128 Restriction0935_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 478848 128 Restriction0935_1_checked index (by omega) (by omega)
  else
    if cut : index < 479104 then
      exact segment_sound _ 478976 128 Restriction0935_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 479104 128 Restriction0935_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
