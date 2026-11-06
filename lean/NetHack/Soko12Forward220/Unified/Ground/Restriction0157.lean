import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0157_0_checked : (List.range' 80384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0157_1_checked : (List.range' 80512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0157_2_checked : (List.range' 80640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0157_3_checked : (List.range' 80768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0157_range (index : Nat) (lower : 80384 ≤ index) (upper : index < 80896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 80640 then
    if cut : index < 80512 then
      exact segment_sound _ 80384 128 Restriction0157_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 80512 128 Restriction0157_1_checked index (by omega) (by omega)
  else
    if cut : index < 80768 then
      exact segment_sound _ 80640 128 Restriction0157_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 80768 128 Restriction0157_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
