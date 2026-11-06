import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0826_0_checked : (List.range' 422912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0826_1_checked : (List.range' 423040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0826_2_checked : (List.range' 423168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0826_3_checked : (List.range' 423296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0826_range (index : Nat) (lower : 422912 ≤ index) (upper : index < 423424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 423168 then
    if cut : index < 423040 then
      exact segment_sound _ 422912 128 Restriction0826_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 423040 128 Restriction0826_1_checked index (by omega) (by omega)
  else
    if cut : index < 423296 then
      exact segment_sound _ 423168 128 Restriction0826_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 423296 128 Restriction0826_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
