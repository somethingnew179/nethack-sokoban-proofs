import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0919_0_checked : (List.range' 470528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0919_1_checked : (List.range' 470656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0919_2_checked : (List.range' 470784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0919_3_checked : (List.range' 470912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0919_range (index : Nat) (lower : 470528 ≤ index) (upper : index < 471040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 470784 then
    if cut : index < 470656 then
      exact segment_sound _ 470528 128 Restriction0919_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 470656 128 Restriction0919_1_checked index (by omega) (by omega)
  else
    if cut : index < 470912 then
      exact segment_sound _ 470784 128 Restriction0919_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 470912 128 Restriction0919_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
