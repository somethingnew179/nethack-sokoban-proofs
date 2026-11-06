import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1861_0_checked : (List.range' 952832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1861_1_checked : (List.range' 952960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1861_2_checked : (List.range' 953088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1861_3_checked : (List.range' 953216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1861_range (index : Nat) (lower : 952832 ≤ index) (upper : index < 953344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 953088 then
    if cut : index < 952960 then
      exact segment_sound _ 952832 128 Restriction1861_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 952960 128 Restriction1861_1_checked index (by omega) (by omega)
  else
    if cut : index < 953216 then
      exact segment_sound _ 953088 128 Restriction1861_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 953216 128 Restriction1861_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
