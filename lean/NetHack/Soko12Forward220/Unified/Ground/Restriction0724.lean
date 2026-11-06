import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0724_0_checked : (List.range' 370688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0724_1_checked : (List.range' 370816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0724_2_checked : (List.range' 370944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0724_3_checked : (List.range' 371072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0724_range (index : Nat) (lower : 370688 ≤ index) (upper : index < 371200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 370944 then
    if cut : index < 370816 then
      exact segment_sound _ 370688 128 Restriction0724_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 370816 128 Restriction0724_1_checked index (by omega) (by omega)
  else
    if cut : index < 371072 then
      exact segment_sound _ 370944 128 Restriction0724_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 371072 128 Restriction0724_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
