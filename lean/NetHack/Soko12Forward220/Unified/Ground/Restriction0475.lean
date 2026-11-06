import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0475_0_checked : (List.range' 243200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0475_1_checked : (List.range' 243328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0475_2_checked : (List.range' 243456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0475_3_checked : (List.range' 243584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0475_range (index : Nat) (lower : 243200 ≤ index) (upper : index < 243712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 243456 then
    if cut : index < 243328 then
      exact segment_sound _ 243200 128 Restriction0475_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 243328 128 Restriction0475_1_checked index (by omega) (by omega)
  else
    if cut : index < 243584 then
      exact segment_sound _ 243456 128 Restriction0475_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 243584 128 Restriction0475_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
