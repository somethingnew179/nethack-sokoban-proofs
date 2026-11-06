import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1506_0_checked : (List.range' 771072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1506_1_checked : (List.range' 771200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1506_2_checked : (List.range' 771328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1506_3_checked : (List.range' 771456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1506_range (index : Nat) (lower : 771072 ≤ index) (upper : index < 771584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 771328 then
    if cut : index < 771200 then
      exact segment_sound _ 771072 128 Restriction1506_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 771200 128 Restriction1506_1_checked index (by omega) (by omega)
  else
    if cut : index < 771456 then
      exact segment_sound _ 771328 128 Restriction1506_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 771456 128 Restriction1506_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
