import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0246_0_checked : (List.range' 125952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0246_1_checked : (List.range' 126080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0246_2_checked : (List.range' 126208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0246_3_checked : (List.range' 126336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0246_range (index : Nat) (lower : 125952 ≤ index) (upper : index < 126464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 126208 then
    if cut : index < 126080 then
      exact segment_sound _ 125952 128 Restriction0246_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 126080 128 Restriction0246_1_checked index (by omega) (by omega)
  else
    if cut : index < 126336 then
      exact segment_sound _ 126208 128 Restriction0246_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 126336 128 Restriction0246_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
