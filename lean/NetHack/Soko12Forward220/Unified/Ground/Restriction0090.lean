import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0090_0_checked : (List.range' 46080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0090_1_checked : (List.range' 46208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0090_2_checked : (List.range' 46336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0090_3_checked : (List.range' 46464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0090_range (index : Nat) (lower : 46080 ≤ index) (upper : index < 46592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 46336 then
    if cut : index < 46208 then
      exact segment_sound _ 46080 128 Restriction0090_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 46208 128 Restriction0090_1_checked index (by omega) (by omega)
  else
    if cut : index < 46464 then
      exact segment_sound _ 46336 128 Restriction0090_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 46464 128 Restriction0090_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
