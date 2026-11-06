import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0461_0_checked : (List.range' 236032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0461_1_checked : (List.range' 236160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0461_2_checked : (List.range' 236288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0461_3_checked : (List.range' 236416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0461_range (index : Nat) (lower : 236032 ≤ index) (upper : index < 236544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 236288 then
    if cut : index < 236160 then
      exact segment_sound _ 236032 128 Restriction0461_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 236160 128 Restriction0461_1_checked index (by omega) (by omega)
  else
    if cut : index < 236416 then
      exact segment_sound _ 236288 128 Restriction0461_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 236416 128 Restriction0461_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
